// Unrestricted rooted, directed closed walks. Repetitions are NEVER rejected.
// Output groups by step profile, equality kernel, and one projection kernel.
#include <cstdint>
#include <iostream>
#include <limits>
#include <map>
#include <stdexcept>
#include <string>
#include <vector>
using namespace std;
struct Edge { int to, axis; };
int main() {
  int n, q, m, distinguished;
  if (!(cin >> n >> q >> m >> distinguished) || n <= 0 || q <= 0 || m < 3 || m > 10)
    throw runtime_error("invalid dimensions");
  vector<int> budget(q), used(q), labels(n, -1), path(m), axes(m);
  for (auto &x : budget) cin >> x; // -1 means unrestricted
  vector<vector<int>> coordinate(n, vector<int>(q));
  for (auto &v : coordinate) for (auto &x : v) cin >> x;
  vector<vector<Edge>> adj(n);
  int e; cin >> e;
  for (int i=0, u, v, a; i<e; ++i) {
    cin >> u >> v >> a;
    if (u<0 || u>=n || v<0 || v>=n || a<0 || a>=q || u==v)
      throw runtime_error("invalid edge");
    adj[u].push_back({v,a});
  }
  map<string, uint64_t> histogram;
  auto emit = [&]() {
    string key;
    for (int a=0; a<q; ++a) { if(a) key += ','; key += to_string(used[a]); }
    key += '|';
    for (int i=0; i<m; ++i) key += char('0'+labels[path[i]]);
    key += '|';
    if (distinguished>=0) {
      map<int,int> first;
      for (int i=0; i<m; ++i) if (axes[i]==distinguished) {
        int v=coordinate[path[i]][distinguished];
        if (!first.count(v)) first[v]=int(first.size());
        key += char('0'+first[v]);
      }
    } else key += '-';
    auto &value=histogram[key];
    if (value==numeric_limits<uint64_t>::max()) throw runtime_error("count overflow");
    ++value;
  };
  for (int root=0; root<n; ++root) {
    labels[root]=0; path[0]=root;
    auto walk = [&](auto &&self, int depth, int current, int distinct) -> void {
      for (auto edge : adj[current]) {
        int a=edge.axis, v=edge.to;
        if (budget[a]>=0 && used[a]>=budget[a]) continue;
        ++used[a]; axes[depth]=a;
        if (depth==m-1) {
          if (v==root) emit();
        } else {
          // The label is bookkeeping for the equality kernel, never a guard.
          bool fresh=labels[v]<0;
          if (fresh) labels[v]=distinct;
          path[depth+1]=v;
          self(self, depth+1, v, distinct+int(fresh));
          if (fresh) labels[v]=-1;
        }
        --used[a];
      }
    };
    walk(walk, 0, root, 1);
    labels[root]=-1;
  }
  for (const auto &[key,value] : histogram) cout << key << ' ' << value << '\n';
}
