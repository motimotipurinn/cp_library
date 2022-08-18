#include <bits/stdc++.h>
#pragma GCC target("avx2")
#pragma GCC optimize("O3")
#pragma GCC optimize("unroll-loops")
#define ll long long
#define int long long
#define rep(i, n) for (int i = 0; i < (int)(n); i++)
#define ALL(a) (a).begin(), (a).end()
#define fore(i, a) for (auto &i : a)
#define MP make_pair
using namespace std;
using ld = long double;
using pll = pair<ll, ll>;
using pdd = pair<ld, ld>;
using Graph = vector<vector<ll>>;
using in = int;
using vin = vector<in>;
using vvin = vector<vector<int>>;
using PQS = priority_queue<int, vector<int>, greater<int>>;
using PQ = priority_queue<int>;
const ll MOD = 998244353;
const ll INF = 1LL << 60;
const int dx[4] = {1, -1, 0, 0};
const int dy[4] = {0, 0, 1, -1};
template <class T>
bool chmin(T &a, T b) {
  if (a > b) {
    a = b;
    return true;
  } else {
    return false;
  }
}
template <typename A, size_t N, typename T>
void Fill(A (&array)[N], const T &val) {
  std::fill((T *)array, (T *)(array + N), val);
}
template <class T>
bool chmax(T &a, T b) {
  if (a < b) {
    a = b;
    return true;
  } else {
    return false;
  }
}
bool cmp(const pll &a, const pll &b) { return a.second > b.second; }
ll GD(ll num) {  //各桁の和
  ll digit = 0;
  while (num != 0) {
    digit += num % 10;
    num /= 10;
  }
  return digit;
}
bool if_integer(ld x) {  //整数判定
  return std::floor(x) == x;
}
bool if_prime(ll x) {
  bool a = true;
  for (ll i = 2; i * i <= x; i++) {
    if (x % i == 0) {
      a = false;
      break;
    }
  }
  if (x == 1) a = false;
  return a;
}
ll gcd(ll x, ll y) {
  if (x == 0) {
    if (y == 0) {
      return 1;
    } else {
      return y;
    }
  }
  if (y == 0) {
    return x;
  }
  if (x % y == 0) {
    return (y);
  } else {
    return (gcd(y, x % y));
  }
}
ll lcm(int x, int y) { return x / gcd(x, y) * y; }
int GetDigit(int num) {
  int digit = 0;
  while (num != 0) {
    num /= 10;
    digit++;
  }
  return digit;
}
template <typename T>
vector<T> compress(vector<T> &X) {
  vector<T> vals = X;
  sort(vals.begin(), vals.end());
  vals.erase(unique(vals.begin(), vals.end()), vals.end());
  for (int i = 0; i < (int)X.size(); i++) {
    X[i] = lower_bound(vals.begin(), vals.end(), X[i]) - vals.begin();
  }
  return vals;
}

template <int MOD>
struct Fp {
  long long val;
  constexpr Fp(long long v = 0) noexcept : val(v % MOD) {
    if (val < 0) val += MOD;
  }
  constexpr int getmod() { return MOD; }
  constexpr Fp operator-() const noexcept { return val ? MOD - val : 0; }
  constexpr Fp operator+(const Fp &r) const noexcept { return Fp(*this) += r; }
  constexpr Fp operator-(const Fp &r) const noexcept { return Fp(*this) -= r; }
  constexpr Fp operator*(const Fp &r) const noexcept { return Fp(*this) *= r; }
  constexpr Fp operator/(const Fp &r) const noexcept { return Fp(*this) /= r; }
  constexpr Fp &operator+=(const Fp &r) noexcept {
    val += r.val;
    if (val >= MOD) val -= MOD;
    return *this;
  }
  constexpr Fp &operator-=(const Fp &r) noexcept {
    val -= r.val;
    if (val < 0) val += MOD;
    return *this;
  }
  constexpr Fp &operator*=(const Fp &r) noexcept {
    val = val * r.val % MOD;
    return *this;
  }
  constexpr Fp &operator/=(const Fp &r) noexcept {
    long long a = r.val, b = MOD, u = 1, v = 0;
    while (b) {
      long long t = a / b;
      a -= t * b;
      swap(a, b);
      u -= t * v;
      swap(u, v);
    }
    val = val * u % MOD;
    if (val < 0) val += MOD;
    return *this;
  }
  constexpr bool operator==(const Fp &r) const noexcept {
    return this->val == r.val;
  }
  constexpr bool operator!=(const Fp &r) const noexcept {
    return this->val != r.val;
  }
  friend constexpr ostream &operator<<(ostream &os, const Fp<MOD> &x) noexcept {
    return os << x.val;
  }
  friend constexpr Fp<MOD> modpow(const Fp<MOD> &a, long long n) noexcept {
    if (n == 0) return 1;
    auto t = modpow(a, n / 2);
    t = t * t;
    if (n & 1) t = t * a;
    return t;
  }
};
using mint = Fp<MOD>;

ll modpow(ll a, ll n) {
  ll res = 1;
  while (n) {
    if (n & 1) res = res * a % MOD;
    a = a * a % MOD;
    n >>= 1;
  }
  return res;
}
struct UnionFind {
  //自身が親であれば、その集合に属する頂点数に-1を掛けたもの
  //そうでなければ親のid
  vector<int> r;
  UnionFind(int N) { r = vector<int>(N, -1); }
  int root(int x) {
    if (r[x] < 0) return x;
    return r[x] = root(r[x]);
  }
  bool unite(int x, int y) {
    x = root(x);
    y = root(y);
    if (x == y) return false;
    if (r[x] > r[y]) swap(x, y);
    r[x] += r[y];
    r[y] = x;
    return true;
  }
  int size(int x) { return -r[root(x)]; }
  bool issame(int x, int y) { return root(x) == root(y); }
};
struct SCC {
  int n;
  vvin G, rG;
  vin order, component;
  vector<bool> used;
  void dfs(int v) {
    used[v] = 1;
    for (auto nv : G[v]) {
      if (!used[nv]) dfs(nv);
    }
    order.push_back(v);
  }
  void rdfs(int v, int k) {
    component[v] = k;
    for (auto nv : rG[v]) {
      if (component[nv] < 0) rdfs(nv, k);
    }
  }
  SCC(vvin &_G) {
    n = _G.size();
    G = _G;
    rG.resize(n);
    component.assign(n, -1);
    used.resize(n);
    rep(v, n) {
      for (auto nv : G[v]) rG[nv].push_back(v);
    }
    rep(v, n) if (!used[v]) dfs(v);
    int k = 0;
    reverse(ALL(order));
    for (auto v : order)
      if (component[v] == -1) rdfs(v, k), k++;
  }
  bool is_same(int u, int v) { return component[u] == component[v]; }
  vvin rebuild() {
    int N = *max_element(ALL(component)) + 1;
    vvin rebuildedG(N);
    set<pll> connected;
    rep(v, N) {
      for (auto nv : G[v]) {
        if (component[v] != component[nv] and !connected.count({v, nv})) {
          connected.insert({v, nv});
          rebuildedG[component[v]].push_back(component[nv]);
        }
      }
    }
    return rebuildedG;
  }
};
signed main() {
  ios::sync_with_stdio(false);
  std::cin.tie(nullptr);
  cout << std::fixed << std::setprecision(50);
  ////////////////////////////
  ///////////////////////////
  in N, M;
  cin >> N >> M;
  Graph G(N);
  rep(i, M) {
    in a, b;
    cin >> a >> b;
    a--;
    b--;
    G[a].push_back(b);
  }
  SCC sc(G);
  in ans = 0;
  vin v(N);
  rep(i, N) { v[sc.component[i]]++; }
  rep(i, N) { ans += v[i] * (v[i] - 1) / 2; }
  cout << ans << endl;
}
//
// rm -rf test/ && oj d
// g++ main.cpp
//  oj t --ignore-spaces-and-newline