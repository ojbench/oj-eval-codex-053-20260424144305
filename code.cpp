#include <bits/stdc++.h>
using namespace std;

namespace Grammar {
enum class TransitionType { Epsilon, a, b };
struct Transition {
  TransitionType type;
  int to;
  Transition(TransitionType t, int v) : type(t), to(v) {}
};

struct NFA {
  int start = 0;
  unordered_set<int> ends;
  vector<vector<Transition>> transitions;

  NFA() = default;

  unordered_set<int> GetEpsilonClosure(unordered_set<int> states) const {
    unordered_set<int> closure;
    queue<int> q;
    for (int s : states) {
      if (!closure.insert(s).second) continue;
      q.push(s);
    }
    while (!q.empty()) {
      int u = q.front(); q.pop();
      if (u < 0 || u >= (int)transitions.size()) continue;
      for (auto &tr : transitions[u]) {
        if (tr.type == TransitionType::Epsilon) {
          if (closure.insert(tr.to).second) q.push(tr.to);
        }
      }
    }
    return closure;
  }

  unordered_set<int> Advance(unordered_set<int> current_states, char character) const {
    unordered_set<int> cur = GetEpsilonClosure(current_states);
    unordered_set<int> next;
    TransitionType want = (character == 'a') ? TransitionType::a : TransitionType::b;
    for (int s : cur) {
      if (s < 0 || s >= (int)transitions.size()) continue;
      for (auto &tr : transitions[s]) {
        if (tr.type == want) next.insert(tr.to);
      }
    }
    return GetEpsilonClosure(next);
  }
};

static NFA MakeSimple(char ch) {
  NFA n;
  n.start = 0;
  n.ends = {1};
  n.transitions.assign(2, {});
  n.transitions[0].push_back({ch == 'a' ? TransitionType::a : TransitionType::b, 1});
  return n;
}

static NFA MakeStar(char ch) {
  NFA n;
  n.start = 0;
  n.ends = {0};
  n.transitions.assign(1, {});
  n.transitions[0].push_back({ch == 'a' ? TransitionType::a : TransitionType::b, 0});
  return n;
}

static NFA MakePlus(char ch) {
  // one or more occurrences
  // states: 0 (start), 1 (loop) end=1; 0 -ch-> 1, 1 -ch-> 1
  NFA n;
  n.start = 0;
  n.ends = {1};
  n.transitions.assign(2, {});
  auto t = (ch == 'a') ? TransitionType::a : TransitionType::b;
  n.transitions[0].push_back({t, 1});
  n.transitions[1].push_back({t, 1});
  return n;
}

static NFA MakeQuestion(char ch) {
  // zero or one
  // states: 0 (start,end), 1; 0 -ch-> 1; end={0,1}
  NFA n;
  n.start = 0;
  n.ends = {0, 1};
  n.transitions.assign(2, {});
  n.transitions[0].push_back({ch == 'a' ? TransitionType::a : TransitionType::b, 1});
  return n;
}

static NFA Concatenate(const NFA &A, const NFA &B) {
  NFA n;
  int offA = 0;
  int offB = (int)A.transitions.size();
  // size = A.size + B.size
  n.start = A.start;
  n.transitions.assign(A.transitions.size() + B.transitions.size(), {});
  // copy A transitions
  for (int i = 0; i < (int)A.transitions.size(); ++i) {
    for (auto &tr : A.transitions[i]) n.transitions[i].push_back(tr);
  }
  // copy B transitions with offset
  for (int i = 0; i < (int)B.transitions.size(); ++i) {
    for (auto &tr : B.transitions[i]) n.transitions[offB + i].push_back({tr.type, offB + tr.to});
  }
  // ends: for each end of A, add epsilon to B.start+offB
  for (int e : A.ends) {
    if (e >= 0 && e < (int)n.transitions.size())
      n.transitions[e].push_back({TransitionType::Epsilon, offB + B.start});
  }
  // ends of concatenation are ends of B (offset)
  for (int e : B.ends) n.ends.insert(offB + e);
  return n;
}

static NFA Union(const NFA &A, const NFA &B) {
  // new start 0 epsilon to A.start+1 and B.start+1
  // shift A by +1, B by +1+|A|
  NFA n;
  int offA = 1;
  int offB = 1 + (int)A.transitions.size();
  int total = 1 + (int)A.transitions.size() + (int)B.transitions.size();
  n.start = 0;
  n.transitions.assign(total, {});
  // epsilon edges from new start
  n.transitions[0].push_back({TransitionType::Epsilon, offA + A.start});
  n.transitions[0].push_back({TransitionType::Epsilon, offB + B.start});
  // copy A
  for (int i = 0; i < (int)A.transitions.size(); ++i) {
    for (auto &tr : A.transitions[i]) n.transitions[offA + i].push_back({tr.type, offA + tr.to});
  }
  // copy B
  for (int i = 0; i < (int)B.transitions.size(); ++i) {
    for (auto &tr : B.transitions[i]) n.transitions[offB + i].push_back({tr.type, offB + tr.to});
  }
  // ends are union of ends(A) shifted and ends(B) shifted
  for (int e : A.ends) n.ends.insert(offA + e);
  for (int e : B.ends) n.ends.insert(offB + e);
  return n;
}

struct RegexChecker {
  NFA nfa;
  explicit RegexChecker(const string &regex) {
    // Parse regex with lowest precedence '|', then concatenation, then postfix (* + ?)
    // No parentheses. Only symbols: a,b,+,*,?,|
    // Strategy: Split by '|', build NFA for each term, union them left-to-right.
    vector<string> terms;
    {
      string cur;
      for (char c : regex) {
        if (c == '|') {
          terms.push_back(cur);
          cur.clear();
        } else cur.push_back(c);
      }
      terms.push_back(cur);
    }
    auto build_term = [&](const string &t) {
      // Build concatenation of factors. Each factor is a base 'a'/'b' possibly followed by +/*/?
      bool first = true;
      NFA acc;
      for (size_t i = 0; i < t.size(); ++i) {
        char c = t[i];
        if (c != 'a' && c != 'b') continue; // skip unexpected
        NFA piece = MakeSimple(c);
        if (i + 1 < t.size()) {
          char op = t[i + 1];
          if (op == '+') { piece = MakePlus(c); ++i; }
          else if (op == '*') { piece = MakeStar(c); ++i; }
          else if (op == '?') { piece = MakeQuestion(c); ++i; }
        }
        if (first) { acc = piece; first = false; }
        else { acc = Concatenate(acc, piece); }
      }
      if (first) {
        // empty term: not expected, but create NFA that accepts nothing
        NFA empty;
        empty.start = 0;
        empty.transitions.assign(1, {});
        return empty;
      }
      return acc;
    };

    bool first = true;
    for (auto &t : terms) {
      NFA part = build_term(t);
      if (first) { nfa = part; first = false; }
      else { nfa = Union(nfa, part); }
    }
  }

  bool Check(const string &str) const {
    unordered_set<int> cur{nfa.start};
    for (char ch : str) {
      cur = nfa.Advance(cur, ch);
      if (cur.empty()) break;
    }
    for (int s : cur) if (nfa.ends.count(s)) return true;
    return false;
  }
};
} // namespace Grammar

int main() {
  ios::sync_with_stdio(false);
  cin.tie(nullptr);

  // Input format assumptions:
  // First line: regex string (only a,b,+,*,?,|) ;
  // Second: integer Q; followed by Q lines each a test string;
  // If Q missing, read remaining lines until EOF and print one line per input.

  string regex;
  if (!getline(cin, regex)) return 0;
  if (regex.size() && regex.back()=='\r') regex.pop_back();
  Grammar::RegexChecker checker(regex);

  string line;
  // Try read integer count; if fail, treat it as a test string and process lines until EOF.
  streampos pos = cin.tellg();
  if (!getline(cin, line)) return 0;
  if (line.size() && line.back()=='\r') line.pop_back();
  bool is_int = true;
  for (char c : line) if (!(c=='-' || (c>='0'&&c<='9') || c==' '||c=='\t')) { is_int=false; break; }
  if (is_int) {
    // parse integer
    stringstream ss(line);
    long long q; if (!(ss >> q)) { is_int = false; }
    if (is_int) {
      for (long long i=0;i<q && getline(cin, line);++i) {
        if (line.size() && line.back()=='\r') line.pop_back();
        cout << (checker.Check(line) ? "Yes" : "No") << "\n";
      }
      return 0;
    }
  }
  // Not an int; process the line as test string, then the rest until EOF
  cout << (checker.Check(line) ? "Yes" : "No") << "\n";
  while (getline(cin, line)) {
    if (line.size() && line.back()=='\r') line.pop_back();
    cout << (checker.Check(line) ? "Yes" : "No") << "\n";
  }
  return 0;
}

