#include <bits/stdc++.h>
#include <ext/pb_ds/assoc_container.hpp>
#include <ext/pb_ds/tree_policy.hpp>

using namespace std;
using namespace __gnu_pbds;

#define fi first
#define se second
#define mp make_pair
#define pb push_back
#define fbo find_by_order
#define ook order_of_key

typedef long long ll;
typedef pair<ll,ll> ii;
typedef vector<int> vi;
typedef long double ld; 
typedef tree<int, null_type, less<int>, rb_tree_tag, tree_order_statistics_node_update> pbds;
typedef set<int>::iterator sit;
typedef map<int,int>::iterator mit;
typedef vector<int>::iterator vit;

//This template is compiled by zscoder.

//O(V^2E) Dinic Flow
//Initialize : MaxFlow<# of vertices, Max Value> M;
template<int MX, ll INF> struct MaxFlow //by yutaka1999, have to define INF and MX (the Max number of vertices)
{
	struct edge
	{
		int to,cap,rev;
		edge(int to=0,int cap=0,int rev=0):to(to),cap(cap),rev(rev){}
	};
	vector <edge> vec[MX];
	int level[MX];
	int iter[MX];
	
	void addedge(int s,int t,int c) //adds an edge of cap c to the flow graph
	{
		int S=vec[s].size(),T=vec[t].size();
		vec[s].push_back(edge(t,c,T));
		vec[t].push_back(edge(s,0,S));
	}
	void bfs(int s)
	{
		memset(level,-1,sizeof(level));
		queue <int> que;
		level[s] = 0;
		que.push(s);
		while (!que.empty())
		{
			int v = que.front();que.pop();
			for(int i=0;i<vec[v].size();i++)
			{
				edge&e=vec[v][i];
				if (e.cap>0&&level[e.to]<0)
				{
					level[e.to]=level[v]+1;
					que.push(e.to);
				}
			}
		}
	}
	ll flow_dfs(int v,int t,ll f)
	{
		if (v==t) return f;
		for(int &i=iter[v];i<vec[v].size();i++)
		{
			edge &e=vec[v][i];
			if (e.cap>0&&level[v]<level[e.to])
			{
				ll d=flow_dfs(e.to,t,min(f,ll(e.cap)));
				if (d>0)
				{
					e.cap-=d;
					vec[e.to][e.rev].cap+=d;
					return d;
				}
			}
		}
		return 0;
	}
	ll maxflow(int s,int t) //finds max flow using dinic from s to t
	{
		ll flow = 0;
		while(1)
		{
			bfs(s);
			if (level[t]<0) return flow;
			memset(iter,0,sizeof(iter));
			while (1)
			{
				ll f=flow_dfs(s,t,INF);
				if(f==0) break;
				flow += f;
			}
		}
	}
};
//End Dinic Flow

//Sparse Table Struct
//SparseTable<ll, 1000001, 20, ll(1e18)> ST;
template<typename TT, int MX, int LG, ll INF> struct SparseTable //Warning : Change query return value manually if needed. INF is the dummy val
{
	TT st[LG][MX];
	TT initial[MX];
	
	TT combine(TT a, TT b) //warning : change if neccesary
	{
		if(a<b) return a;
		return b;
	}
	
	SparseTable()
	{
		for(int i = 0; i < MX; i++) initial[i] = INF;
	}
	
	void init()
	{
		for(ll j = 0; j < LG; j++)
		{
			for(ll i = 0; i < MX; i++)
			{
				st[j][i] = INF;
				if(i + (1<<j) - 1 < MX)
				{
					if(j == 0) st[j][i] = initial[i];
					else st[j][i] = combine(st[j-1][i], st[j-1][i + (1<<(j-1))]);
				}
			}
		}
	}
	
	TT query(int l, int r)
	{
		int k = 31 - __builtin_clz(r-l);
		if(l==r) k=0;
		return combine(st[k][l], st[k][r - (1<<k) + 1]);
	}
};

//Segment Tree Lazy Prop begin. node and update are just samples and should be changed according to problem
//use init, upd, and query function ([l, r])
//REMEMBER TO SET WIDTH WHEN INIT LEAVES!
template<typename T, typename U> struct SegmentTree //by socketnaut. see http://codeforces.com/blog/entry/20528
{
    int S, H;
 
    T zero;
    vector<T> value;
 
    U noop;
    vector<bool> dirty; //a.k.a is_lazy
    vector<U> prop; //the update array
 
    SegmentTree<T, U>(int _S, T _zero = T(), U _noop = U()) {
        zero = _zero, noop = _noop;
        for (S = 1, H = 1; S < _S; ) S *= 2, H++;
 
        value.resize(2*S, zero);
        dirty.resize(2*S, false);
        prop.resize(2*S, noop);
    }
 
    void init(vector<T> &leaves) {
        copy(leaves.begin(), leaves.end(), value.begin() + S);
 
        for (int i = S - 1; i > 0; i--)
            value[i] = value[2 * i] + value[2 * i + 1];
    }
 
    void apply(int i, U &update) {
        value[i] = update(value[i]);
        if(i < S) {
            prop[i] = prop[i] + update;
            dirty[i] = true;
        }
    }
 
    void rebuild(int i) {
        for (int l = i/2; l; l /= 2) {
            T combined = value[2*l] + value[2*l+1];
            value[l] = prop[l](combined);
        }
    }
 
    void propagate(int i) {
        for (int h = H; h > 0; h--) {
            int l = i >> h;
 
            if (dirty[l]) {
                apply(2*l, prop[l]);
                apply(2*l+1, prop[l]);
 
                prop[l] = noop;
                dirty[l] = false;
            }
        }
    }
 
    void upd(int i, int j, U update) {
        i += S, j += S;
        propagate(i), propagate(j);
 
        for (int l = i, r = j; l <= r; l /= 2, r /= 2) {
            if((l&1) == 1) apply(l++, update);
            if((r&1) == 0) apply(r--, update);
        }
 
        rebuild(i), rebuild(j);
    }
 
    T query(int i, int j){
        i += S, j += S;
        propagate(i), propagate(j);
 
        T res_left = zero, res_right = zero;
        for(; i <= j; i /= 2, j /= 2){
            if((i&1) == 1) res_left = res_left + value[i++];
            if((j&1) == 0) res_right = value[j--] + res_right;
        }
        return res_left + res_right;
    }
};

struct node 
{
    int sum, width;
    
    node operator+(const node &n) 
    {
        node tmp;
        tmp.sum = sum + n.sum;
        tmp.width = width + n.width;
        return tmp;
    }    
};

struct update {
    bool type; // 0 for add, 1 for reset
    int value;

    node operator()(const node &n) 
    {
		node tmp;
        if (type) 
        {
			tmp.sum = n.width * value;
			tmp.width = n.width;
		}
        else 
        {
			tmp.sum = n.sum + n.width * value;
			tmp.width = n.width;
		}
		return tmp;
    }

    update operator+(const update &u) 
    {
		update tmp;
        if (u.type) return u; //since it's a reset
        tmp.type = type;
        tmp.value = value + u.value;
        return tmp;
    }
};
//Segment Tree end

//DSU start
struct DSU
{
	int S;
	
	struct node
	{
		int p; ll sum;
	};
	vector<node> dsu;
	
	DSU(int n)
	{
		S = n;
		for(int i = 0; i < n; i++)
		{
			node tmp;
			tmp.p = i; tmp.sum = 0;
			dsu.pb(tmp);
		}
	}
	
	void reset(int n)
	{
		dsu.clear();
		S = n;
		for(int i = 0; i < n; i++)
		{
			node tmp;
			tmp.p = i; tmp.sum = 0;
			dsu.pb(tmp);
		}
	}
	
	int rt(int u)
	{
		if(dsu[u].p == u) return u;
		dsu[u].p = rt(dsu[u].p);
		return dsu[u].p;
	}
	
	void merge(int u, int v)
	{
		u = rt(u); v = rt(v);
		if(u == v) return ;
		if(rand()&1) swap(u, v);
		dsu[v].p = u;
		dsu[u].sum += dsu[v].sum;
	}
	
	bool sameset(int u, int v)
	{
		if(rt(u) == rt(v)) return true;
		return false;
	}
	
	ll getstat(int u)
	{
		return dsu[rt(u)].sum;
	}
};
//DSU end

//Order Stat Tree start 
struct PBDS
{
	tree<ii, null_type, less<ii>, rb_tree_tag, tree_order_statistics_node_update> t;
	int timer;
	
	PBDS(){timer = 0;}
	void insert(int x)
	{
		t.insert(mp(x, timer));
		timer++;
	}
	
	int lower(int x)
	{
		return t.order_of_key(ii(x, -1));
	}
	
	void del(int x) //make sure x exists
	{
		ii tmp = (*t.find_by_order(lower(x)));
		t.erase(tmp);
	}
	
	int higher(int x)
	{
		int tmp = lower(x+1);
		return (int(t.size()) - tmp);
	}
};
//End Order Stat Tree

//Start NT
struct NumberTheory
{
	vector<ll> primes;
	vector<bool> prime;
	vector<ll> totient;
	vector<ll> sumdiv;
	vector<ll> mobius;
	vector<ll> bigdiv;
	void Sieve(ll n)
	{
		prime.assign(n+1, 1);
		prime[1] = false;
		for(ll i = 2; i <= n; i++)
		{
			if(prime[i])
			{
				primes.pb(i);
				for(ll j = i*2; j <= n; j += i)
				{
					prime[j] = false;
				}
			}
		}
	}
	
	ll phi(ll x)
	{
		map<ll,ll> pf;
		ll num = 1; ll num2 = x;
		for(ll i = 0; primes[i]*primes[i] <= x; i++)
		{
			if(x%primes[i]==0)
			{
				num2/=primes[i];
				num*=(primes[i]-1);
			}
			while(x%primes[i]==0)
			{
				x/=primes[i];
				pf[primes[i]]++;
			}
		}
		if(x>1)
		{
			pf[x]++; num2/=x; num*=(x-1);
		}
		x = 1;
		num*=num2;
		return num;
	}
	
	bool isprime(ll x)
	{
		if(x==1) return false;
		for(ll i = 0; primes[i]*primes[i] <= x; i++)
		{
			if(x%primes[i]==0) return false;
		}
		return true;
	}

	void SievePhi(ll n)
	{
		totient.resize(n+1);
		for (int i = 1; i <= n; ++i) totient[i] = i;
		for (int i = 2; i <= n; ++i)
		{
			if (totient[i] == i)
			{
				for (int j = i; j <= n; j += i)
				{
					totient[j] -= totient[j] / i;
				}
			}
		}
	}
	void SieveMob(ll n)
	{
		mobius.resize(n+1,0);
		mobius[1] = 1;
		for (int i = 2; i <= n; ++i) {
			if (prime[i]) {
				mobius[i] = -1;				//i is prime
			}
			for (int j = 0; j < primes.size () && i * primes[j] <= n; ++j) {
				if (i % primes[j] == 0) {
					mobius[i * primes[j]] = 0;//prime[j] divides i
					break;
				} else {
					mobius[i * primes[j]] = mobius[i] * -1;	//prime[j] does not divide i
				}
			}
		}
	}
	
	void SieveSumDiv(ll n)
	{
		sumdiv.resize(n+1);
		for(int i = 1; i <= n; ++i)
		{
			for(int j = i; j <= n; j += i)
			{
				sumdiv[j] += i;
			}
		}
	}
	
	ll getPhi(ll n)
	{
		return totient[n];
	}
	
	ll getSumDiv(ll n)
	{
		return sumdiv[n];
	}
	
	ll modpow(ll a, ll b, ll mod)
	{
		ll r = 1;
		if(b < 0) b += mod*100000LL;
		while(b)
		{
			if(b&1) r = (r*a)%mod;
			a = (a*a)%mod;
			b>>=1;
		}
		return r;
	}
	
	ll inv(ll a, ll mod)
	{
		return modpow(a, mod - 2, mod);
	}
	
	ll invgeneral(ll a, ll mod)
	{
		ll ph = phi(mod);
		ph--;
		return modpow(a, ph, mod);
	}
	
	void getpf(vector<ii>& pf, ll n)
	{
		for(ll i = 0; primes[i]*primes[i] <= n; i++)
		{
			int cnt = 0;
			while(n%primes[i]==0)
			{
				n/=primes[i]; cnt++;
			}
			if(cnt>0) pf.pb(ii(primes[i], cnt));
		}
		if(n>1)
		{
			pf.pb(ii(n, 1));
		}
	}

	//ll op;
	void getDiv(vector<ll>& div, vector<ii>& pf, ll n, int i)
	{
		//op++;
		ll x, k;
		if(i >= pf.size()) return ;
		x = n;
		for(k = 0; k <= pf[i].se; k++)
		{
			if(i==int(pf.size())-1) div.pb(x);
			getDiv(div, pf, x, i + 1);
			x *= pf[i].fi;
		}
	}
};
//End NT

//Start Fenwick (by Christopherboo)
struct Fenwick
{
	vector<ll> t;
    Fenwick(int n)
    {
        t.assign(n+1,0);
    }
    void reset(int n)
    {
		t.assign(n+1, 0);
	}
    void update(int p, ll v)
    {
        for (; p < (int)t.size(); p += (p&(-p))) t[p] += v;
    }
    ll query(int r) //finds [1, r] sum
    {                     
        ll sum = 0;
        for (; r; r -= (r&(-r))) sum += t[r];
        return sum;
    }
    ll query(int l, int r) //finds [l, r] sum
    {
		if(l == 0) return query(r);
		return query(r) - query(l-1);
	}
};
//End Fenwick

//Start FenwickRange (by Christopherboo)
struct FenwickRange
{
	vector<ll> fw, fw2;
    int siz;
    FenwickRange(int N)
    {
        fw.assign(N+1,0);
        fw2.assign(N+1,0);
        siz = N+1;
    }
    void reset(int N)
    {
		fw.assign(N+1,0);
        fw2.assign(N+1,0);
        siz = N+1;
	}
    void update(int l, int r, ll val) //[l, r] + val
    {    
        for (int tl = l; tl < siz; tl += (tl&(-tl)))
        {
            fw[tl] += val, fw2[tl] -= val * ll(l - 1);
        }
        for (int tr = r + 1; tr < siz; tr += (tr&(-tr)))
        {
            fw[tr] -= val, fw2[tr] += val * ll(r);
        }
    }
    ll sum(int r) //[1, r]
    {                         
        ll res = 0;
        for (int tr = r; tr; tr -= (tr&(-tr)))
        {
            res += fw[tr] * ll(r) + fw2[tr];
        }
        return res;
    }
    ll query(ll l, ll r)
    {
		if(l == 0) return sum(r);
		else return sum(r)-sum(l-1);
	}
};
//End FenwickRange

//Start Fenwick2D (by Christopherboo)
struct Fenwick2D
{
	int R, C;
    vector< vector<ll> > fw;
    Fenwick2D(int r, int c) 
    {
        R = r; C = c;
        fw.assign(R+1, vector<ll>(C+1,0));
    }
    void reset(int r, int c)
    {
		R = r; C = c;
        fw.assign(R+1, vector<ll>(C+1,0));
	}
    void update(int row, int col, ll val) 
    {
        for (int r = row; r < R; r += (r&(-r)))
        {
            for(int c = col; c < C; c += (c&(-c))) 
            {
                fw[r][c] += val;
            }
        }
    }
    ll sum(int row, int col)   // inclusive
    {               
        ll res = 0;
        for (int r = row; r; r -= (r&(-r)))
        {
            for(int c = col; c; c -= (c&(-c))) 
            {
                res += fw[r][c];
            }
        }
        return res;
    }
    ll query(int x1, int y1, int x2, int y2) 
    { 
        return sum(x2, y2) - sum(x1-1, y2) - sum(x2, y1-1) + sum(x1-1, y1-1);
    }
};
//End Fenwick2D

//Begin Matrix (from Um_nik's submission)
const int mod = int(1e9) + 7;
const int DIM = 52;

struct Matrix {
  int a[DIM][DIM];
  int *operator [] (int r) { return a[r]; };

  Matrix(int x = 0) {
    memset(a, 0, sizeof a);
    if (x)
    {
		for(int i = 0; i < DIM; i++) a[i][i] = x;
	}
  }
} const I(1);

Matrix operator * (Matrix A, Matrix B) {
  const ll mod2 = ll(mod) * mod;
  Matrix C;
 for(int i = 0; i < DIM; i++)
 {
	 for(int j = 0; j < DIM; j++)
	 {
		ll w = 0;
		for(int k = 0; k < DIM; k++)
		{
			w += ll(A[i][k]) * B[k][j];
			if (w >= mod2) w -= mod2;
		}
    C[i][j] = w % mod;
	}
  }
  return C;
}

Matrix operator ^ (Matrix A, ll b) {
  Matrix R = I;
  for (; b > 0; b /= 2) {
    if (b % 2) R = R*A;
    A = A*A;
  }
  return R;
}
//End Matrix

//Begin suffix auto
//Most of this are from here : https://saisumit.wordpress.com/2016/01/26/suffix-automaton/
template<int MAXLEN> struct SuffixAutomaton //check if it works (works only for 'a' - 'z', for general alphabet sets see code from SUBST1
{
	struct state 
	{
		int len, link;
		int nxt[26];
	};
  
	state st[MAXLEN*2];
	int sz, last;
	bool terminal[MAXLEN*2];
	
	void reset()
	{
		for(int i = 0; i < MAXLEN*2; i++)
		{
			st[i].len = 0; st[i].link = -1; 
			for(int j = 0; j < 26; j++)
			{
				st[i].nxt[j] = 0;
			}
		}
		sz = last = 0;
		st[0].len = 0;
		st[0].link = -1;
		++sz;
	}
	
	void sa_init() 
	{
		for(int i = 0; i < MAXLEN*2; i++)
		{
			st[i].len = 0; st[i].link = -1; 
			for(int j = 0; j < 26; j++)
			{
				st[i].nxt[j] = 0;
			}
		}
		sz = last = 0;
		st[0].len = 0;
		st[0].link = -1;
		++sz;
	}
	  
	void sa_extend (char d)
	{
		int c = (d-'a');
		int cur = sz++;
		st[cur].len = st[last].len + 1;
		int p;
		for (p=last; (p!=-1 && st[p].nxt[c]==0); p=st[p].link)
		{
			st[p].nxt[c] = cur;
		}
		if (p == -1)
		{
			st[cur].link = 0;
		}
		else 
		{
			int q = st[p].nxt[c];
			if (st[p].len + 1 == st[q].len)
			{
				st[cur].link = q;
			}
			else 
			{
				int clone = sz++;
				st[clone].len = st[p].len + 1;
				for(int i = 0; i < 26; i++) {st[clone].nxt[i] = st[q].nxt[i];}
				st[clone].link = st[q].link;
				for (; p!=-1 && st[p].nxt[c]==q; p=st[p].link)
				{
					st[p].nxt[c] = clone;
				}
				st[q].link = st[cur].link = clone;
			}
		}
		last = cur;
	}
	
	void build(string &s)
	{
		sa_init();
		for(int i = 0; i < s.length(); i++)
		{
			sa_extend(s[i]);
		}
	}
	
	void constructTerminal()
	{
		memset(terminal, false, sizeof(terminal));
		int p = last;
		while(p>0)
		{
			terminal[p] = true;
			p = st[p].link;
		}
	}
	
	vector<int> dst; 
	
	void initDistSub()
	{
		dst.assign(MAXLEN*2+3, 0);
	}
	
	int DistSub(int ver)
	{ 
		int tp = 1;
	  
	    if(dst[ver]) return dst[ver];
	  
	    for(int i=0;i<26;i++)
	    {
		 	if(st[ver].nxt[i])
			 {
			 	tp+= DistSub(st[ver].nxt[i]);
			 } 
	    }
	  
	    dst[ver] = tp;
	    if(ver==0) dst[ver]--;
	    return dst[ver];
	}
	
	int GetDistSub()
	{
		initDistSub();
		return DistSub(0); //if empty string counts, don't -1
	}
	
	bool isSubstring(string &p, string &s) //test if p is a substring of s (bug check)
	{
		int cur = 0;
		for(int i = 0; i < p.size(); i++)
		{
			if(st[cur].nxt[p[i]-'a'] == 0) return false;
			cur = st[cur].nxt[p[i]-'a'];
		}
		return true;
	}
	
	bool isSuffix(string &p, string &s) //true if p is a suffix of s. Must use constructTerminal first! (bug check)
	{
		int cur = 0;
		for(int i = 0; i < p.size(); i++)
		{
			if(st[cur].nxt[p[i]-'a'] == 0) return false;
			cur = st[cur].nxt[p[i]-'a'];
		}
		if(terminal[cur]) return true;
	}
	
	vi totalLength;
	
	ll leSub(int ver)
	{
		int tp = 0;
		if(totalLength[ver]) return totalLength[ver];
		for(int i=0;i<26;i++)
		{
			if(st[ver].nxt[i])
			{
				tp = leSub(st[ver].nxt[i]) + dst[st[ver].nxt[i]];
			}
		}
		totalLength[ver] = tp;
		return tp;
	}
	
	ll totalLengthDist() //must run GetDistSub() before use
	{
		totalLength.resize(MAXLEN*2, 0);
		return leSub(0);
	}
	
	void klex(ll &k, string &ans) //run GetDistSub() first. finds the k-th lexicographical smallest substring of the string and store answer in s. Start at node 0.
	{
		int now = 0;
		while(1)
		{
			for(int c = 0; c < 26; c++)
			{
				if(st[now].nxt[c])
				{
					if(k <= dst[st[now].nxt[c]])
					{
						now = st[now].nxt[c];
						ans += char(c+'a');
						break;
					}
					else
					{
						k -= dst[st[now].nxt[c]];
					}
				}
			}
			//cerr << now << ' ' << k << '\n';
			k--;
			if(k==0) break;
		}
	}
	
	int LCS(string &t) //Returns size of longest Common Substring of s (the current string) and t. Can be modified to return the string itself. 
	{
		int v = 0, l = 0; 
		int best = 0; int bestpos = 0;
		for(int i = 0; i < int(t.length()); i++)
		{
			while(v && !st[v].nxt[t[i]-'a'])
			{
				v = st[v].link;
				l = st[v].len;
			}
			if(st[v].nxt[t[i]-'a'])
			{
				v = st[v].nxt[t[i]-'a'];
				l++;
			}
			if(l > best)
			{
				best = l; bestpos = i;
			}
		}
		//best string is from bestpos - best + 1 to bestpos;
		return best;		
	}
};
//End suffix auto

//Begin Suffix + LCP Array
string globalstr;

bool smaller_first_char(int a, int b)
{
  return globalstr[a] < globalstr[b];
}

//pos[i] is the real suffix array
struct SuffixLCPArray //to work for general alphabet remove the - 'a'
{	
	vi rnk, pos, cnt, nxt;
	vector<bool> bh, b2h;
	
	void buildSA(const string& str)
	{
		globalstr = str;
		int n = str.length();
		rnk.assign(n,0);
		pos.assign(n,0);
		cnt.assign(n,0);
		nxt.assign(n,0);
		bh.assign(n,0);
		b2h.assign(n,0);
		for (int i=0; i<n; ++i)
		{
			pos[i] = i;
		}
		sort(pos.begin(), pos.end(), smaller_first_char);
		for (int i=0; i<n; ++i)
		{
			bh[i] = i == 0 || str[pos[i]] != str[pos[i-1]];
			b2h[i] = false;
		}		 
		for (int h = 1; h < n; h <<= 1)
		{
			int buckets = 0;
			for (int i=0, j; i < n; i = j)
			{
				j = i + 1;
				while (j < n && !bh[j]) j++;
				nxt[i] = j;
				buckets++;
			}
			if (buckets == n) break; 
		 
			for (int i = 0; i < n; i = nxt[i])
			{
			  cnt[i] = 0;
			  for (int j = i; j < nxt[i]; ++j)
			  {
				rnk[pos[j]] = i;
			  }
			}
		 
			cnt[rnk[n - h]]++;
			b2h[rnk[n - h]] = true;
			for (int i = 0; i < n; i = nxt[i])
			{
			  for (int j = i; j < nxt[i]; ++j)
			  {
				int s = pos[j] - h;
				if (s >= 0){
				  int head = rnk[s];
				  rnk[s] = head + cnt[head]++;
				  b2h[rnk[s]] = true;
				}
			  }
			  for (int j = i; j < nxt[i]; ++j)
			  {
				int s = pos[j] - h;
				if (s >= 0 && b2h[rnk[s]]){
				  for (int k = rnk[s]+1; !bh[k] && b2h[k]; k++)
				  {
					  b2h[k] = false;
				  }
				}
			  }
			}
			for (int i=0; i<n; ++i)
			{
			  pos[rnk[i]] = i;
			  bh[i] = (bh[i] || b2h[i]);
			}
	    }
		for (int i=0; i<n; ++i)
		{
			rnk[pos[i]] = i;
		}
	}
	
	vi rank;
	vi lcp;
	
	void reset()
	{
		rnk.clear(); pos.clear(); bh.clear(); b2h.clear(); cnt.clear(); nxt.clear(); rank.clear(); lcp.clear();
	}
	// - lcp[i] = length of the longest common prefix of suffix
	//   pos[i] and suffix pos[i-1]
	// - lcp[0] = 0
	void buildLCP(string &s)
	{
		int n = s.length();
		lcp.assign(n+1,0);
		for (int i=0; i<n; ++i) rnk[pos[i]] = i;
		lcp[0] = 0;
		for (int i=0, h=0; i<n; ++i)
		{
			if (rnk[i] > 0)
			{
			  int j = pos[rnk[i]-1];
			  while (i + h < n && j + h < n && s[i+h] == s[j+h])
			  {
				  h++;
			  }
			  lcp[rnk[i]] = h;
			  if (h > 0) h--;
			}
		}
	}
};
//End Suffix + LCP Array

//Start Convex Hull Trick (by christopherboo)
struct ConvexHull //insert increasing slope, queries increasing!
{
    struct Line 
    {
        ll m, c;

        Line (ll _m, ll _c) : m(_m), c(_c) {}

        ll pass(ll x) {
            return m * x + c;
        }
    };
    deque<Line> d;
    bool irrelevant(Line Z) 
    {
        if (int(d.size()) < 2) return false;
    
        Line X = d[int(d.size())-2], Y = d[int(d.size())-1];

        return (X.c - Z.c) * (Y.m - X.m) <= (X.c - Y.c) * (Z.m - X.m);
    }
    void push_line(ll m, ll c) 
    {
        Line l = Line(m,c);
        while (irrelevant(l)) d.pop_back();
        d.push_back(l);
    }
    ll query(ll x) {
        while (int(d.size()) > 1 && (d[0].c - d[1].c <= x * (d[1].m - d[0].m))) d.pop_front();
        return d.front().pass(x);
    }
};

struct ConvexHull //insert increasing slope, queries arbitrary!
{
    struct Line 
    {
        ll m, c;

        Line (ll _m, ll _c) : m(_m), c(_c) {}

        ll pass(ll x) {
            return m * x + c;
        }
    };
    deque<Line> d;
    bool irrelevant(Line Z) 
    {
        if (int(d.size()) < 2) return false;
    
        Line X = d[int(d.size())-2], Y = d[int(d.size())-1];

        return (X.c - Z.c) * (Y.m - X.m) <= (X.c - Y.c) * (Z.m - X.m);
    }
    void push_line(ll m, ll c) 
    {
        Line l = Line(m,c);
        while (irrelevant(l)) d.pop_back();
        d.push_back(l);
    }
    ll query(ll x)
    {
		if(d.empty()) return 0;
		ll ans = max(d[0].pass(x), d[int(d.size())-1].pass(x));
		int lo = 0; int hi = int(d.size())-2;
		while(lo<=hi)
		{
			int mid=(lo+hi)>>1;
			ll v1 = d[mid].pass(x);
			ll v2 = d[mid+1].pass(x);
			ans=max(ans,v1);
			ans=max(ans,v2);
			if(v1<=v2)
			{
				lo=mid+1;
			}
			else
			{
				hi=mid-1;
			}
		}
		return ans;
	}
};
//End Convex Hull Trick

// (Basic Algos)
struct Graph
{
	struct edge
	{
		int v; ll weight;
	};
	vector<vector<edge> > adj;
	int n;
	
	Graph(int _n)
	{
		adj.resize(_n);
		n = _n;
	}
	
	void addedge(int u, int v, ll c)
	{
		edge tmp;
		tmp.v = v; tmp.weight = c;
		adj[u].pb(tmp);
		tmp.v = u;
		adj[v].pb(tmp);
	}
	
	void reset()
	{
		adj.clear();
	}
	
	vector<ll> dist;
	vi par;
	
	void bfs(int s)
	{
		ll INFI = ll(1e18);
		dist.assign(n, INFI);
		par.assign(n, -1);
		dist[s] = 0; par[s] = -1;
		queue<int> q; q.push(s);
		while(!q.empty())
		{
			int u = q.front(); q.pop();
			for(int i = 0; i < adj[u].size(); i++)
			{
				int v = adj[u][i].v;
				if(dist[v] >= INFI)
				{
					dist[v] = dist[u] + 1;
					par[v] = u;
					q.push(v);
				}
			}
		}
	}
	
	void bfs01(int s)
	{
		ll INFI = ll(1e18);
		dist.assign(n, INFI);
		par.assign(n, -1);
		dist[s] = 0; par[s] = -1;
		deque<int> q; q.pb(s);
		while(!q.empty())
		{
			int u = q.front(); q.pop_front();
			for(int i = 0; i < adj[u].size(); i++)
			{
				int v = adj[u][i].v; ll w = adj[u][i].weight;
				if(dist[v] >= INFI)
				{
					if(w == 1)
					{
						dist[v] = dist[u] + 1;
						par[v] = u;
						q.push_back(v);
					}
					else
					{
						dist[v] = dist[u];
						par[v] = u;
						q.push_front(v);
					}
				}
			}
		}
	}
	
	void dijkstra(int s)
	{
		ll INFI = ll(1e18);
		dist.clear();
		dist.assign(n, INFI);
		par.assign(n, -1);
		dist[s] = 0; par[s] = -1;
		priority_queue<pair<ll,ll> , vector<pair<ll,ll> >, greater<pair<ll,ll> > > pq;
		pq.push(mp(0, s));
		while(!pq.empty())
		{
			int u = pq.top().se; ll d = pq.top().fi; pq.pop();
			if(d>dist[u]) continue;
			for(int i = 0; i < adj[u].size(); i++)
			{
				int v = adj[u][i].v; ll w = adj[u][i].weight;
				if(d + w < dist[v])
				{
					dist[v] = d + w;
					par[v] = u;
					pq.push(mp(dist[v], v));
				}
			}
		}
	}
	
	vector<vector<ll> > d;
	
	void Floyd()
	{
		ll INFIN = ll(1e18);
		d.resize(n);
		for(int i = 0; i < n; i++)
		{
			d[i].assign(n, INFIN);
		}
		for(int i = 0; i < n; i++)
		{
			for(int j = 0; j < adj[i].size(); j++)
			{
				d[i][adj[i][j].v] = adj[i][j].weight;
			}
			d[i][i] = 0;
		}
		for(int k = 0; k < n; k++)
		{
			for(int i = 0; i < n; i++)
			{
				for(int j = 0; j < n; j++)
				{
					d[i][j] = min(d[i][j], d[i][k] + d[k][j]);
				}
			}
		}
	}
	
	bool BellmanFord(int s) //returns true if negative weight cycle exists
	{
		ll INFI = ll(1e18);
		dist.assign(n, INFI);
		par.assign(n, -1);
		dist[s] = 0;
		for(int step = 1; step <= n; step++)
		{
			for(int i = 0; i < n; i++)
			{
				for(int j = 0; j < adj[i].size(); j++)
				{
					int u = i; int v = adj[i][j].v; ll w = adj[i][j].weight;
					if(dist[v] > dist[u] + w)
					{
						if(step == n)
						{
							return true;
						}
						dist[v] = dist[u] + w;
					}
				}
			}
		}
		return false;
	}
	
	ll shortest(int s, int e) //returns the distance by Dijkstra
	{
		return dist[e];
	}
	
	vector<pair<ll, ii> > edges;
	
	ll Kruskal()
	{
		DSU dsu(n);
		for(int i = 0; i < n; i++)
		{
			for(int j = 0; j < adj[i].size(); j++)
			{
				int u = i; int v = adj[i][j].v; ll w = adj[i][j].weight;
				edges.pb(mp(w, mp(u, v)));
			}
		}
		sort(edges.begin(), edges.end());
		ll ans = 0; int cnt = 0;
		for(int i = 0; i < edges.size(); i++)
		{
			int u = edges[i].se.fi; int v = edges[i].se.se;
			if(dsu.sameset(u, v)) continue;
			dsu.merge(u, v);
			cnt++; ans += edges[i].fi;
			if(cnt >= n - 1) break;
		}
		return ans;
	}
};
//End 

//Tree
struct Tree
{
	struct data
	{
		ll w;
	};
	
	struct node
	{
		int p; //parent
		ll w; //modify for different problems
	};
	
	struct edge
	{
		int v; data dat;
	};
	
	vector<vector<edge> > adj;
	int n;
	
	Tree(int _n)
	{
		adj.resize(_n);
		n = _n;
	}
	
	vi level;
	vi depth;
	vi h;
	vi euler;
	vi firstocc;
	vector<vi> rmqtable;
	vi subsize;
	vi start; vi en;
	vector<vector<node> > st;
	
	void addedge(int u, int v)
	{
		edge tmp; tmp.v = v;
		adj[u].pb(tmp);
		tmp.v = u;
		adj[v].pb(tmp);
	}
	
	void reset(int _n)
	{
		adj.clear();
		level.clear();
		depth.clear();
		euler.clear();
		rmqtable.clear();
		subsize.clear();
		start.clear();
		en.clear();
		st.clear();
		firstocc.clear();
		adj.resize(_n);
		n = _n;
	}
	
	void dfssub(int u, int p)
	{
		subsize[u] = 1;
		for(int i = 0; i < adj[u].size(); i++)
		{
			int v = adj[u][i].v;
			if(v == p) continue;
			dfssub(v, u);
			subsize[u] += subsize[v];
		}
	}
	
	void calcsub()
	{
		subsize.resize(n);
		dfssub(0, -1);
	}
	
	int timer;
	
	void dfsstartend(int u, int p)
	{
		start[u] = ++timer;
		if(p == -1) h[u] = 0;
		else h[u] = h[p] + 1;
		for(int i = 0; i < adj[u].size(); i++)
		{
			int v = adj[u][i].v;
			if(v == p) continue;
			dfsstartend(v, u);
		}
		en[u] = ++timer;
	}
	
	void calcstartend()
	{
		timer = 0;
		start.resize(n); en.resize(n); h.resize(n);
		dfsstartend(0, -1);
	}
	
	int eulercnt;
	
	void dfseuler(int u, int p)
	{
		euler[eulercnt] = u; eulercnt++;
		if(p == -1) {depth[u] = 0;}
		else {depth[u] = depth[p] + 1;}
		firstocc[u] = eulercnt-1;
		for(int i = 0; i < adj[u].size(); i++)
		{
			int v = adj[u][i].v;
			if(v == p) continue ;
			dfseuler(v, u);
			euler[eulercnt] = u; eulercnt++;
		}
	}
	
	void calceuler()
	{
		eulercnt = 0;
		level.assign(2*n+1, 0);
		euler.assign(2*n+1, 0);
		depth.assign(n, 0);
		firstocc.resize(n);
		dfseuler(0, -1);
	}

	void filllevel()
	{
		int LG = 0;
		while((1<<LG) <= n*2) LG++;
		rmqtable.resize(LG);
		for(int i = 0; i < LG; i++) rmqtable[i].resize(eulercnt);
		for(int i = 0; i < eulercnt; i++)
		{
			level[i] = depth[euler[i]];
		}
		level[eulercnt] = 1000000000;
		for(int j = 0; j < LG; j++)
		{
			for(int i = 0; i < eulercnt; i++)
			{
				rmqtable[j][i] = eulercnt;
				if(i + (1<<j) - 1 < eulercnt)
				{
					if(j == 0)
					{
						rmqtable[j][i] = i;
					}
					else
					{
						if(level[rmqtable[j - 1][i]] < level[rmqtable[j-1][i + (1<<(j-1))]])
						{
							rmqtable[j][i] = rmqtable[j-1][i];
						}
						else
						{
							rmqtable[j][i] = rmqtable[j-1][i + (1<<(j-1))];
						}
					}
				}
			}
		}
	}

	int rmq(int l, int r)
	{
		int k = 31 - __builtin_clz(r-l);
		//cout << l << ' ' << r << ' ' << rmqtable[l][k] << ' ' << rmqtable[r - (1<<k) + 1][k] << endl;
		if(level[rmqtable[k][l]] < level[rmqtable[k][r - (1<<k) + 1]])
		{
			return rmqtable[k][l];
		}
		else
		{
			return rmqtable[k][r - (1<<k) + 1];
		}
	}

	int lcaeuler(int u, int v)
	{
		if(firstocc[u] > firstocc[v]) swap(u, v);
		//cerr << firstocc[u] << ' ' << firstocc[v] << ' ' << rmq(firstocc[u], firstocc[v]) << ' ' << euler[rmq(firstocc[u], firstocc[v])] << endl;
		return euler[rmq(firstocc[u], firstocc[v])];
	}
	
	bool insub(int u, int v) //is u in the subtree of v?
	{
		if(start[v] <= start[u] && en[u] <= en[v]) return true;
		return false;
	}
	
	void dfspar(int u, int p)
	{
		//cerr << u << ' ' << p << '\n';
		st[0][u].p = p;
		if(p == -1) h[u] = 0;
		else h[u] = h[p] + 1;
		for(int i = 0; i < adj[u].size(); i++)
		{
			int v = adj[u][i].v;
			if(v == p) continue;
			dfspar(v, u);
		}
	}
	
	int LOG;
	
	void calcpar()
	{
		h.resize(n);
		int LG = 0; LOG = 0;
		while((1<<LG) <= n) {LG++; LOG++;}
		st.resize(LG);
		for(int i = 0; i < LG; i++)
		{
			st[i].resize(n);
		}
		dfspar(0, -1);
		//cerr << "HER" << ' ' << LG << endl;
		for(int i = 1; i < LG; i++)
		{
			for(int j = 0; j < n; j++)
			{
				if(st[i-1][j].p == -1) st[i][j].p = -1;
				else st[i][j].p = st[i-1][st[i-1][j].p].p;
			}
		}
	}
	
	int getpar(int u, ll k)
	{
		for(int i = LOG - 1; i >= 0; i--)
		{
			if(k&(1<<i))
			{
				u = st[i][u].p;
			}
		}
		return u;
	}
	
	int lca(int u, int v)
	{
		if(h[u] > h[v]) swap(u, v);
		for(int i = LOG - 1; i >= 0; i--)
		{
			if(st[i][v].p != -1 && h[st[i][v].p] >= h[u])
			{
				v = st[i][v].p;
			}
		}
		if(u == v) return u;
		for(int i = LOG - 1; i >= 0; i--)
		{
			if(st[i][v].p != -1 && st[i][v].p != st[i][u].p)
			{
				u = st[i][u].p;
				v = st[i][v].p;
			}
		}
		return st[0][u].p;
	}

	int distance(int u, int v)
	{
		int lc = lca(u, v);
		return (h[u]+h[v]-2*h[lc]);
	}
};
//End Tree

//Start Treap (see https://threads-iiith.quora.com/Treaps-One-Tree-to-Rule-em-all-Part-2)
struct Treap
{
	struct node
	{
		int prior,siz;
		ll val;//value stored in the array
		ll sum;//whatever info you want to maintain in segtree for each node
		ll lazy;//whatever lazy update you want to do
		struct node *l,*r;
	};
	
	typedef node* pnode;
	
	int sz(pnode t)
	{
		return t?t->siz:0;
	}
	void upd_sz(pnode t)
	{
		if(t)t->siz=sz(t->l)+1+sz(t->r);
	}
	void lazy(pnode t)
	{
		if(!t || !t->lazy)return;
		t->val+=t->lazy;//operation of lazy
		t->sum+=t->lazy*sz(t);
		if(t->l)t->l->lazy+=t->lazy;//propagate lazy
		if(t->r)t->r->lazy+=t->lazy;
		t->lazy=0;
	}
	void reset(pnode t)
	{
		if(t)t->sum = t->val;//no need to reset lazy coz when we call this lazy would itself be propagated
	}
	void combine(pnode& t,pnode l,pnode r){//combining two ranges of segtree
		if(!l || !r)return void(t = l?l:r);
		t->sum = l->sum + r->sum;
	}
	void operation(pnode t){//operation of segtree
		if(!t)return;
		reset(t);//reset the value of current node assuming it now represents a single element of the array
		lazy(t->l);lazy(t->r);//imp:propagate lazy before combining t->l,t->r;
		combine(t,t->l,t);
		combine(t,t,t->r);
	}
	void split(pnode t,pnode &l,pnode &r,int pos,int add=0){
		if(!t)return void(l=r=NULL);
		lazy(t);
		int curr_pos = add + sz(t->l);
		if(curr_pos<=pos)//element at pos goes to left subtree(l)
			split(t->r,t->r,r,pos,curr_pos+1),l=t;
		else 
			split(t->l,l,t->l,pos,add),r=t;
		upd_sz(t);
		operation(t);
	}
	void merge(pnode &t,pnode l,pnode r){ //l->leftarray,r->rightarray,t->resulting array
		lazy(l);lazy(r);
		if(!l || !r) t = l?l:r;
		else if(l->prior>r->prior)merge(l->r,l->r,r),t=l;
		else    merge(r->l,l,r->l),t=r;
		upd_sz(t);
		operation(t);
	}
	pnode init(int val){
		pnode ret = (pnode)malloc(sizeof(node));
		ret->prior=rand();ret->siz=1;
		ret->val=val;
		ret->sum=val;ret->lazy=0;
		return ret;
	}
	int range_query(pnode t,int l,int r){//[l,r]
		pnode L,mid,R;
		split(t,L,mid,l-1);
		split(mid,t,R,r-l);//note: r-l!!
		int ans = t->sum;
		merge(mid,L,t);
		merge(t,mid,R);
		return ans;
	}
	void range_update(pnode t,int l,int r,ll val){//[l,r]
		pnode L,mid,R;
		split(t,L,mid,l-1);
		split(mid,t,R,r-l);//note: r-l!!
		t->lazy+=val; //lazy_update
		merge(mid,L,t);
		merge(t,mid,R);
	}
};
//End Treap

//Begin Geometry (see daizhenyang's submission to 280A)
const double eps=1e-8;
const double pi=acos(-1.0);
const double inf=1e20;
const int maxp=111111;
int dblcmp(double d)
{
    if (fabs(d)<eps)return 0;
    return d>eps?1:-1;
}
inline double sqr(double x){return x*x;}
struct point 
{
    double x,y;
    point(){}
    point(double _x,double _y):
    x(_x),y(_y){};
    void input()
    {
        scanf("%lf%lf",&x,&y);
    }
    void output()
    {
        printf("%.2f %.2f\n",x,y);
    }
    bool operator==(point a)const
    {
        return dblcmp(a.x-x)==0&&dblcmp(a.y-y)==0;
    }
    bool operator<(point a)const
    {
        return dblcmp(a.x-x)==0?dblcmp(y-a.y)<0:x<a.x;
    }
    double len()
    {
        return hypot(x,y);
    }
    double len2()
    {
        return x*x+y*y;
    }
    double distance(point p)
    {
        return hypot(x-p.x,y-p.y);
    }
    point add(point p)
    {
        return point(x+p.x,y+p.y);
    }
    point sub(point p)
    {
        return point(x-p.x,y-p.y);
    }
    point mul(double b)
    {
        return point(x*b,y*b);
    }
    point div(double b)
    {
        return point(x/b,y/b);
    }
    double dot(point p)
    {
        return x*p.x+y*p.y;
    }
    double det(point p)
    {
        return x*p.y-y*p.x;
    }
    double rad(point a,point b)
    {
        point p=*this;
        return fabs(atan2(fabs(a.sub(p).det(b.sub(p))),a.sub(p).dot(b.sub(p))));
    }
    point trunc(double r)
    {
        double l=len();
        if (!dblcmp(l))return *this;
        r/=l;
        return point(x*r,y*r);
    }
    point rotleft()
    {
        return point(-y,x);
    }
    point rotright()
    {
        return point(y,-x);
    }
    point rotate(point p,double angle)//绕点p逆时针旋转angle角度 
    {
        point v=this->sub(p);
        double c=cos(angle),s=sin(angle);
        return point(p.x+v.x*c-v.y*s,p.y+v.x*s+v.y*c);
    }        
};
struct line 
{
    point a,b;
    line(){}
    line(point _a,point _b)
    {
        a=_a;
        b=_b;
    }
    bool operator==(line v)
    {
        return (a==v.a)&&(b==v.b);
    }
    //倾斜角angle 
    line(point p,double angle)
    {
        a=p;
        if (dblcmp(angle-pi/2)==0)
        {
            b=a.add(point(0,1));
        }
        else 
        {
            b=a.add(point(1,tan(angle)));
        }
    }       
    //ax+by+c=0
    line(double _a,double _b,double _c)
    {
        if (dblcmp(_a)==0)
        {
            a=point(0,-_c/_b);
            b=point(1,-_c/_b);
        }
        else if (dblcmp(_b)==0)
        {
            a=point(-_c/_a,0);
            b=point(-_c/_a,1);
        }
        else 
        {
            a=point(0,-_c/_b);
            b=point(1,(-_c-_a)/_b);
        }
    }
    void input()
    {
        a.input();
        b.input();
    }
    void adjust()
    {
        if (b<a)swap(a,b);
    }
    double length()
    {
        return a.distance(b);
    }
    double angle()//直线倾斜角 0<=angle<180 
    {
        double k=atan2(b.y-a.y,b.x-a.x);
        if (dblcmp(k)<0)k+=pi;
        if (dblcmp(k-pi)==0)k-=pi;
        return k;
    }
    //点和线段关系
    //1 在逆时针
    //2 在顺时针
    //3 平行
    int relation(point p)
    {
        int c=dblcmp(p.sub(a).det(b.sub(a)));
        if (c<0)return 1;
        if (c>0)return 2;
        return 3;
    }
    bool pointonseg(point p)
    {
        return dblcmp(p.sub(a).det(b.sub(a)))==0&&dblcmp(p.sub(a).dot(p.sub(b)))<=0;
    }
    bool parallel(line v)
    {
        return dblcmp(b.sub(a).det(v.b.sub(v.a)))==0;
    }
    //2 规范相交
    //1 非规范相交
    //0 不相交 
    int segcrossseg(line v)
    {
        int d1=dblcmp(b.sub(a).det(v.a.sub(a)));
        int d2=dblcmp(b.sub(a).det(v.b.sub(a)));
        int d3=dblcmp(v.b.sub(v.a).det(a.sub(v.a)));
        int d4=dblcmp(v.b.sub(v.a).det(b.sub(v.a)));
        if ((d1^d2)==-2&&(d3^d4)==-2)return 2;
        return (d1==0&&dblcmp(v.a.sub(a).dot(v.a.sub(b)))<=0||
                d2==0&&dblcmp(v.b.sub(a).dot(v.b.sub(b)))<=0||
                d3==0&&dblcmp(a.sub(v.a).dot(a.sub(v.b)))<=0||
                d4==0&&dblcmp(b.sub(v.a).dot(b.sub(v.b)))<=0);        
    }        
    int linecrossseg(line v)//*this seg v line
    {
        int d1=dblcmp(b.sub(a).det(v.a.sub(a)));
        int d2=dblcmp(b.sub(a).det(v.b.sub(a)));
        if ((d1^d2)==-2)return 2;
        return (d1==0||d2==0);
    }
    //0 平行
    //1 重合
    //2 相交 
    int linecrossline(line v)
    {
        if ((*this).parallel(v))
        {
            return v.relation(a)==3;
        }
        return 2;
    }
    point crosspoint(line v)
    {
        double a1=v.b.sub(v.a).det(a.sub(v.a));
        double a2=v.b.sub(v.a).det(b.sub(v.a));
        return point((a.x*a2-b.x*a1)/(a2-a1),(a.y*a2-b.y*a1)/(a2-a1));
    }
    double dispointtoline(point p)
    {
        return fabs(p.sub(a).det(b.sub(a)))/length();
    }
    double dispointtoseg(point p)
    {
        if (dblcmp(p.sub(b).dot(a.sub(b)))<0||dblcmp(p.sub(a).dot(b.sub(a)))<0)
        {
            return min(p.distance(a),p.distance(b));
        }
        return dispointtoline(p);
    }
    point lineprog(point p)
    {
        return a.add(b.sub(a).mul(b.sub(a).dot(p.sub(a))/b.sub(a).len2()));
    }
    point symmetrypoint(point p)
    {
        point q=lineprog(p);
        return point(2*q.x-p.x,2*q.y-p.y);
    }   
};
struct circle 
{
    point p;
    double r;
    circle(){}
    circle(point _p,double _r):
    p(_p),r(_r){};
    circle(double x,double y,double _r):
    p(point(x,y)),r(_r){};
    circle(point a,point b,point c)//三角形的外接圆 (circumcircle)
    {
        p=line(a.add(b).div(2),a.add(b).div(2).add(b.sub(a).rotleft())).crosspoint(line(c.add(b).div(2),c.add(b).div(2).add(b.sub(c).rotleft())));
        r=p.distance(a);
    }
    circle(point a,point b,point c,bool t)//三角形的内切圆 (incircle)
    {
        line u,v;
        double m=atan2(b.y-a.y,b.x-a.x),n=atan2(c.y-a.y,c.x-a.x);
        u.a=a;
        u.b=u.a.add(point(cos((n+m)/2),sin((n+m)/2)));
        v.a=b;
        m=atan2(a.y-b.y,a.x-b.x),n=atan2(c.y-b.y,c.x-b.x);
        v.b=v.a.add(point(cos((n+m)/2),sin((n+m)/2)));
        p=u.crosspoint(v);
        r=line(a,b).dispointtoseg(p);
    }
    void input()
    {
        p.input();
        scanf("%lf",&r);
    }
    void output()
    {
        printf("%.2lf %.2lf %.2lf\n",p.x,p.y,r);
    }
    bool operator==(circle v)
    {
        return ((p==v.p)&&dblcmp(r-v.r)==0);
    }
    bool operator<(circle v)const
    {
        return ((p<v.p)||(p==v.p)&&dblcmp(r-v.r)<0);
    }
    double area()
    {
        return pi*sqr(r);
    }
    double circumference()
    {
        return 2*pi*r;
    }
    //0 圆外
    //1 圆上
    //2 圆内 
    int relation(point b)
    {
        double dst=b.distance(p);
        if (dblcmp(dst-r)<0)return 2;
        if (dblcmp(dst-r)==0)return 1;
        return 0;
    }
    int relationseg(line v)
    {
        double dst=v.dispointtoseg(p);
        if (dblcmp(dst-r)<0)return 2;
        if (dblcmp(dst-r)==0)return 1;
        return 0;
    }
    int relationline(line v)
    {
        double dst=v.dispointtoline(p);
        if (dblcmp(dst-r)<0)return 2;
        if (dblcmp(dst-r)==0)return 1;
        return 0;
    }
    //过a b两点 半径r的两个圆 
    int getcircle(point a,point b,double r,circle&c1,circle&c2)
    {
        circle x(a,r),y(b,r);
        int t=x.pointcrosscircle(y,c1.p,c2.p);
        if (!t)return 0;
        c1.r=c2.r=r;
        return t;
    }
    //与直线u相切 过点q 半径r1的圆 
    int getcircle(line u,point q,double r1,circle &c1,circle &c2)
    {
        double dis=u.dispointtoline(q);
        if (dblcmp(dis-r1*2)>0)return 0;
        if (dblcmp(dis)==0)
        {
            c1.p=q.add(u.b.sub(u.a).rotleft().trunc(r1));
            c2.p=q.add(u.b.sub(u.a).rotright().trunc(r1));
            c1.r=c2.r=r1;
            return 2;
        }
        line u1=line(u.a.add(u.b.sub(u.a).rotleft().trunc(r1)),u.b.add(u.b.sub(u.a).rotleft().trunc(r1)));
        line u2=line(u.a.add(u.b.sub(u.a).rotright().trunc(r1)),u.b.add(u.b.sub(u.a).rotright().trunc(r1)));
        circle cc=circle(q,r1);
        point p1,p2;
        if (!cc.pointcrossline(u1,p1,p2))cc.pointcrossline(u2,p1,p2);
        c1=circle(p1,r1);
        if (p1==p2)
        {
            c2=c1;return 1;
        }
        c2=circle(p2,r1);
        return 2;
    }
    //同时与直线u,v相切 半径r1的圆 
    int getcircle(line u,line v,double r1,circle &c1,circle &c2,circle &c3,circle &c4)
    {
        if (u.parallel(v))return 0;
        line u1=line(u.a.add(u.b.sub(u.a).rotleft().trunc(r1)),u.b.add(u.b.sub(u.a).rotleft().trunc(r1)));
        line u2=line(u.a.add(u.b.sub(u.a).rotright().trunc(r1)),u.b.add(u.b.sub(u.a).rotright().trunc(r1)));
        line v1=line(v.a.add(v.b.sub(v.a).rotleft().trunc(r1)),v.b.add(v.b.sub(v.a).rotleft().trunc(r1)));
        line v2=line(v.a.add(v.b.sub(v.a).rotright().trunc(r1)),v.b.add(v.b.sub(v.a).rotright().trunc(r1)));
        c1.r=c2.r=c3.r=c4.r=r1;
        c1.p=u1.crosspoint(v1);
        c2.p=u1.crosspoint(v2);
        c3.p=u2.crosspoint(v1);
        c4.p=u2.crosspoint(v2);
        return 4;
    }
    //同时与不相交圆cx,cy相切 半径为r1的圆
    int getcircle(circle cx,circle cy,double r1,circle&c1,circle&c2)
    {
        circle x(cx.p,r1+cx.r),y(cy.p,r1+cy.r);
        int t=x.pointcrosscircle(y,c1.p,c2.p);
        if (!t)return 0;
        c1.r=c2.r=r1;
        return t;
    }
    int pointcrossline(line v,point &p1,point &p2)//求与线段交要先判断relationseg  
    {
        if (!(*this).relationline(v))return 0;
        point a=v.lineprog(p);
        double d=v.dispointtoline(p);
        d=sqrt(r*r-d*d);
        if (dblcmp(d)==0)
        {
            p1=a;
            p2=a;
            return 1;
        }
        p1=a.sub(v.b.sub(v.a).trunc(d));
        p2=a.add(v.b.sub(v.a).trunc(d));
        return 2;
    }
    //5 相离
    //4 外切
    //3 相交
    //2 内切
    //1 内含 
    int relationcircle(circle v)
    {
        double d=p.distance(v.p);
        if (dblcmp(d-r-v.r)>0)return 5;
        if (dblcmp(d-r-v.r)==0)return 4;
        double l=fabs(r-v.r);
        if (dblcmp(d-r-v.r)<0&&dblcmp(d-l)>0)return 3;
        if (dblcmp(d-l)==0)return 2;
        if (dblcmp(d-l)<0)return 1;
    }
    int pointcrosscircle(circle v,point &p1,point &p2)
    {
        int rel=relationcircle(v);
        if (rel==1||rel==5)return 0;
        double d=p.distance(v.p);
        double l=(d+(sqr(r)-sqr(v.r))/d)/2;
        double h=sqrt(sqr(r)-sqr(l));
        p1=p.add(v.p.sub(p).trunc(l).add(v.p.sub(p).rotleft().trunc(h)));
        p2=p.add(v.p.sub(p).trunc(l).add(v.p.sub(p).rotright().trunc(h)));
        if (rel==2||rel==4)
        {
            return 1;
        }
        return 2;
    }
    //过一点做圆的切线 (先判断点和圆关系) 
    int tangentline(point q,line &u,line &v)
    {
        int x=relation(q);
        if (x==2)return 0;
        if (x==1)
        {
            u=line(q,q.add(q.sub(p).rotleft()));
            v=u;
            return 1;
        }
        double d=p.distance(q);
        double l=sqr(r)/d;
        double h=sqrt(sqr(r)-sqr(l));
        u=line(q,p.add(q.sub(p).trunc(l).add(q.sub(p).rotleft().trunc(h))));
        v=line(q,p.add(q.sub(p).trunc(l).add(q.sub(p).rotright().trunc(h))));
        return 2;
    }
    double areacircle(circle v)
    {
        int rel=relationcircle(v); 
        if (rel>=4)return 0.0;
        if (rel<=2)return min(area(),v.area());
        double d=p.distance(v.p);
        double hf=(r+v.r+d)/2.0;
        double ss=2*sqrt(hf*(hf-r)*(hf-v.r)*(hf-d));
        double a1=acos((r*r+d*d-v.r*v.r)/(2.0*r*d));
        a1=a1*r*r;
        double a2=acos((v.r*v.r+d*d-r*r)/(2.0*v.r*d));
        a2=a2*v.r*v.r;
        return a1+a2-ss;
    }
    double areatriangle(point a,point b)
    {
        if (dblcmp(p.sub(a).det(p.sub(b))==0))return 0.0;
        point q[5];
        int len=0;
        q[len++]=a;
        line l(a,b);
        point p1,p2;
        if (pointcrossline(l,q[1],q[2])==2)
        {
            if (dblcmp(a.sub(q[1]).dot(b.sub(q[1])))<0)q[len++]=q[1];
            if (dblcmp(a.sub(q[2]).dot(b.sub(q[2])))<0)q[len++]=q[2];
        }
        q[len++]=b;
        if (len==4&&(dblcmp(q[0].sub(q[1]).dot(q[2].sub(q[1])))>0))swap(q[1],q[2]);
        double res=0;
        int i;
        for (i=0;i<len-1;i++)
        {
            if (relation(q[i])==0||relation(q[i+1])==0)
            {
                double arg=p.rad(q[i],q[i+1]);
                res+=r*r*arg/2.0;
            }
            else 
            {
                res+=fabs(q[i].sub(p).det(q[i+1].sub(p))/2.0);
            }
        }
        return res;
    }
};
struct polygon 
{
    int n;
    point p[maxp];
    line l[maxp];
    void input()
    {
        n=4;
        for (int i=0;i<n;i++)
        {
            p[i].input();
        }
    }
    void add(point q)
    {
        p[n++]=q;
    }
    void getline()
    {
        for (int i=0;i<n;i++)
        {
            l[i]=line(p[i],p[(i+1)%n]);
        }
    }
    struct cmp
    {
        point p;
        cmp(const point &p0){p=p0;}
        bool operator()(const point &aa,const point &bb)
        {
            point a=aa,b=bb;
            int d=dblcmp(a.sub(p).det(b.sub(p)));
            if (d==0)
            {
                return dblcmp(a.distance(p)-b.distance(p))<0;
            }
            return d>0;
        }
    };
    void norm()
    {
        point mi=p[0];
        for (int i=1;i<n;i++)mi=min(mi,p[i]);
        sort(p,p+n,cmp(mi));
    }
    void getconvex(polygon &convex)
    {
        int i,j,k;
        sort(p,p+n);
        convex.n=n;
        for (i=0;i<min(n,2);i++)
        {
            convex.p[i]=p[i];
        }
        if (n<=2)return;
        int &top=convex.n;
        top=1;
        for (i=2;i<n;i++)
        {
            while (top&&convex.p[top].sub(p[i]).det(convex.p[top-1].sub(p[i]))<=0)
                top--;
            convex.p[++top]=p[i];
        }
        int temp=top;
        convex.p[++top]=p[n-2];
        for (i=n-3;i>=0;i--)
        {
            while (top!=temp&&convex.p[top].sub(p[i]).det(convex.p[top-1].sub(p[i]))<=0)
                top--;
            convex.p[++top]=p[i];
        }
    }
    bool isconvex()
    {
        bool s[3];
        memset(s,0,sizeof(s));
        int i,j,k;
        for (i=0;i<n;i++)
        {
            j=(i+1)%n;
            k=(j+1)%n;
            s[dblcmp(p[j].sub(p[i]).det(p[k].sub(p[i])))+1]=1;
            if (s[0]&&s[2])return 0;
        }
        return 1;
    }
    //3 点上
    //2 边上
    //1 内部
    //0 外部 
    int relationpoint(point q)
    {
        int i,j;
        for (i=0;i<n;i++)
        {
            if (p[i]==q)return 3;
        }
        getline();
        for (i=0;i<n;i++)
        {
            if (l[i].pointonseg(q))return 2;
        }
        int cnt=0;
        for (i=0;i<n;i++)
        {
            j=(i+1)%n;
            int k=dblcmp(q.sub(p[j]).det(p[i].sub(p[j])));
            int u=dblcmp(p[i].y-q.y);
            int v=dblcmp(p[j].y-q.y);
            if (k>0&&u<0&&v>=0)cnt++;
            if (k<0&&v<0&&u>=0)cnt--;
        }
        return cnt!=0;
    }
    //1 在多边形内长度为正 
    //2 相交或与边平行
    //0 无任何交点 
    int relationline(line u)
    {
        int i,j,k=0;
        getline();
        for (i=0;i<n;i++)
        {
            if (l[i].segcrossseg(u)==2)return 1;
            if (l[i].segcrossseg(u)==1)k=1;
        }
        if (!k)return 0;
        vector<point>vp; 
        for (i=0;i<n;i++)
        {
            if (l[i].segcrossseg(u))
            {
                if (l[i].parallel(u))
                {
                    vp.pb(u.a);
                    vp.pb(u.b);
                    vp.pb(l[i].a);
                    vp.pb(l[i].b);
                    continue;
                }
                vp.pb(l[i].crosspoint(u));
            }
        }
        sort(vp.begin(),vp.end());
        int sz=vp.size();
        for (i=0;i<sz-1;i++)
        {
            point mid=vp[i].add(vp[i+1]).div(2);
            if (relationpoint(mid)==1)return 1;
        }
        return 2;
    }
    //直线u切割凸多边形左侧 
    //注意直线方向 
    void convexcut(line u,polygon &po)
    {
        int i,j,k;
        int &top=po.n;
        top=0;
        for (i=0;i<n;i++)
        {
            int d1=dblcmp(p[i].sub(u.a).det(u.b.sub(u.a)));
            int d2=dblcmp(p[(i+1)%n].sub(u.a).det(u.b.sub(u.a)));
            if (d1>=0)po.p[top++]=p[i];
            if (d1*d2<0)po.p[top++]=u.crosspoint(line(p[i],p[(i+1)%n]));
        }
    }
    double getcircumference()
    {
        double sum=0;
        int i;
        for (i=0;i<n;i++)
        {
            sum+=p[i].distance(p[(i+1)%n]);
        }
        return sum;
    }
    double getarea()
    {
        double sum=0;
        int i;
        for (i=0;i<n;i++)
        {
            sum+=p[i].det(p[(i+1)%n]);
        }
        return fabs(sum)/2;
    }
    bool getdir()//1代表逆时针 0代表顺时针 
    {
        double sum=0;
        int i;
        for (i=0;i<n;i++)
        {
            sum+=p[i].det(p[(i+1)%n]);
        }
        if (dblcmp(sum)>0)return 1;
        return 0;
    }
    point getbarycentre()
    {
        point ret(0,0);
        double area=0;
        int i;
        for (i=1;i<n-1;i++)
        {
            double tmp=p[i].sub(p[0]).det(p[i+1].sub(p[0]));
            if (dblcmp(tmp)==0)continue;
            area+=tmp;
            ret.x+=(p[0].x+p[i].x+p[i+1].x)/3*tmp;
            ret.y+=(p[0].y+p[i].y+p[i+1].y)/3*tmp;
        }
        if (dblcmp(area))ret=ret.div(area);
        return ret;
    }
    double areacircle(circle c)
    {
        int i,j,k,l,m;
        double ans=0;
        for (i=0;i<n;i++)
        {
            int j=(i+1)%n;
            if (dblcmp(p[j].sub(c.p).det(p[i].sub(c.p)))>=0)
            {
                ans+=c.areatriangle(p[i],p[j]);
            }
            else 
            {
                ans-=c.areatriangle(p[i],p[j]);
            }
        }
        return fabs(ans);
    }
    //多边形和圆关系
    //0 一部分在圆外
    //1 与圆某条边相切
    //2 完全在圆内 
    int relationcircle(circle c)
    {
        getline();
        int i,x=2;
        if (relationpoint(c.p)!=1)return 0;
        for (i=0;i<n;i++)
        {
            if (c.relationseg(l[i])==2)return 0;
            if (c.relationseg(l[i])==1)x=1;
        }
        return x;
    }
    void find(int st,point tri[],circle &c)
    {
        if (!st)
        {
            c=circle(point(0,0),-2);
        }
        if (st==1)
        {
            c=circle(tri[0],0);
        }
        if (st==2)
        {
            c=circle(tri[0].add(tri[1]).div(2),tri[0].distance(tri[1])/2.0);
        }
        if (st==3)
        {
            c=circle(tri[0],tri[1],tri[2]);
        }
    }
    void solve(int cur,int st,point tri[],circle &c)
    {
        find(st,tri,c);
        if (st==3)return;
        int i;
        for (i=0;i<cur;i++)
        {
            if (dblcmp(p[i].distance(c.p)-c.r)>0)
            {
                tri[st]=p[i];
                solve(i,st+1,tri,c);
            }
        }
    }
    circle mincircle()//点集最小圆覆盖
    {
        random_shuffle(p,p+n);
        point tri[4];
        circle c;
        solve(n,0,tri,c);
        return c;
    }
    int circlecover(double r)//单位圆覆盖 
    {
        int ans=0,i,j;
        vector<pair<double,int> >v;
        for (i=0;i<n;i++)
        {
            v.clear();
            for (j=0;j<n;j++)if (i!=j)
            {
                point q=p[i].sub(p[j]);
                double d=q.len();
                if (dblcmp(d-2*r)<=0)
                {
                    double arg=atan2(q.y,q.x);
                    if (dblcmp(arg)<0)arg+=2*pi;
                    double t=acos(d/(2*r));
                    v.push_back(make_pair(arg-t+2*pi,-1));
                    v.push_back(make_pair(arg+t+2*pi,1));
                }
            }
            sort(v.begin(),v.end());
            int cur=0;
            for (j=0;j<v.size();j++)
            {
                if (v[j].second==-1)++cur;
                else --cur;
                ans=max(ans,cur);
            }
        }
        return ans+1;
    }           
    int pointinpolygon(point q)//点在凸多边形内部的判定 
    {
        if (getdir())reverse(p,p+n);
        if (dblcmp(q.sub(p[0]).det(p[n-1].sub(p[0])))==0)
        {
            if (line(p[n-1],p[0]).pointonseg(q))return n-1;
            return -1;
        }
        int low=1,high=n-2,mid;
        while (low<=high)
        {
            mid=(low+high)>>1;
            if (dblcmp(q.sub(p[0]).det(p[mid].sub(p[0])))>=0&&dblcmp(q.sub(p[0]).det(p[mid+1].sub(p[0])))<0)
            {
                polygon c;
                c.p[0]=p[mid];
                c.p[1]=p[mid+1];
                c.p[2]=p[0];
                c.n=3;
                if (c.relationpoint(q))return mid;
                return -1;
            }
            if (dblcmp(q.sub(p[0]).det(p[mid].sub(p[0])))>0)
            {
                low=mid+1;
            }
            else 
            {
                high=mid-1;
            }
        }
        return -1;
    }   
};
struct polygons
{
    vector<polygon>p;
    polygons()
    {
        p.clear();
    }
    void clear()
    {
        p.clear();
    }
    void push(polygon q)
    {
        if (dblcmp(q.getarea()))p.pb(q);
    }
    vector<pair<double,int> >e;
    void ins(point s,point t,point X,int i)
    {
        double r=fabs(t.x-s.x)>eps?(X.x-s.x)/(t.x-s.x):(X.y-s.y)/(t.y-s.y);
        r=min(r,1.0);r=max(r,0.0);
        e.pb(mp(r,i));
    }
    double polyareaunion()
    {
        double ans=0.0;
        int c0,c1,c2,i,j,k,w;
        for (i=0;i<p.size();i++)
        {
            if (p[i].getdir()==0)reverse(p[i].p,p[i].p+p[i].n);
        }
        for (i=0;i<p.size();i++)
        {
            for (k=0;k<p[i].n;k++)
            {
                point &s=p[i].p[k],&t=p[i].p[(k+1)%p[i].n];
                if (!dblcmp(s.det(t)))continue;
                e.clear();
                e.pb(mp(0.0,1));
                e.pb(mp(1.0,-1));
                for (j=0;j<p.size();j++)if (i!=j)
                {
                    for (w=0;w<p[j].n;w++)
                    {
                        point a=p[j].p[w],b=p[j].p[(w+1)%p[j].n],c=p[j].p[(w-1+p[j].n)%p[j].n];
                        c0=dblcmp(t.sub(s).det(c.sub(s)));
                        c1=dblcmp(t.sub(s).det(a.sub(s)));
                        c2=dblcmp(t.sub(s).det(b.sub(s)));
                        if (c1*c2<0)ins(s,t,line(s,t).crosspoint(line(a,b)),-c2);
                        else if (!c1&&c0*c2<0)ins(s,t,a,-c2);
                        else if (!c1&&!c2)
                        {
                            int c3=dblcmp(t.sub(s).det(p[j].p[(w+2)%p[j].n].sub(s)));
                            int dp=dblcmp(t.sub(s).dot(b.sub(a)));
                            if (dp&&c0)ins(s,t,a,dp>0?c0*((j>i)^(c0<0)):-(c0<0));
                            if (dp&&c3)ins(s,t,b,dp>0?-c3*((j>i)^(c3<0)):c3<0);
                        }
                    }
                }
                sort(e.begin(),e.end());
                int ct=0;
                double tot=0.0,last;
                for (j=0;j<e.size();j++)
                {
                    if (ct==2)tot+=e[j].first-last;
                    ct+=e[j].second;
                    last=e[j].first;
                }
                ans+=s.det(t)*tot;
            }
        }
        return fabs(ans)*0.5;
    }
};
const int maxn=500;
struct circles 
{
    circle c[maxn];
    double ans[maxn];//ans[i]表示被覆盖了i次的面积 
    double pre[maxn];
    int n;
    circles(){}
    void add(circle cc)
    {
        c[n++]=cc;
    }
    bool inner(circle x,circle y)
    {
        if (x.relationcircle(y)!=1)return 0;
        return dblcmp(x.r-y.r)<=0?1:0;
    }
    void init_or()//圆的面积并去掉内含的圆 
    {
        int i,j,k=0;
        bool mark[maxn]={0};
        for (i=0;i<n;i++)
        {
            for (j=0;j<n;j++)if (i!=j&&!mark[j])
            {
                if ((c[i]==c[j])||inner(c[i],c[j]))break;
            }
            if (j<n)mark[i]=1;
        }
        for (i=0;i<n;i++)if (!mark[i])c[k++]=c[i];
        n=k;
    }
    void init_and()//圆的面积交去掉内含的圆 
    {
        int i,j,k=0;
        bool mark[maxn]={0};
        for (i=0;i<n;i++)
        {
            for (j=0;j<n;j++)if (i!=j&&!mark[j])
            {
                if ((c[i]==c[j])||inner(c[j],c[i]))break;
            }
            if (j<n)mark[i]=1;
        }
        for (i=0;i<n;i++)if (!mark[i])c[k++]=c[i];
        n=k;
    }
    double areaarc(double th,double r)
    {
        return 0.5*sqr(r)*(th-sin(th));
    }
    void getarea()
    {
        int i,j,k;
        memset(ans,0,sizeof(ans));
        vector<pair<double,int> >v;
        for (i=0;i<n;i++)
        {
            v.clear();
            v.push_back(make_pair(-pi,1));
            v.push_back(make_pair(pi,-1));
            for (j=0;j<n;j++)if (i!=j)
            {
                point q=c[j].p.sub(c[i].p);
                double ab=q.len(),ac=c[i].r,bc=c[j].r;
                if (dblcmp(ab+ac-bc)<=0)
                {
                    v.push_back(make_pair(-pi,1));
                    v.push_back(make_pair(pi,-1));
                    continue;
                }
                if (dblcmp(ab+bc-ac)<=0)continue;
                if (dblcmp(ab-ac-bc)>0) continue;
                double th=atan2(q.y,q.x),fai=acos((ac*ac+ab*ab-bc*bc)/(2.0*ac*ab));
                double a0=th-fai;
                if (dblcmp(a0+pi)<0)a0+=2*pi;
                double a1=th+fai;
                if (dblcmp(a1-pi)>0)a1-=2*pi;
                if (dblcmp(a0-a1)>0)
                {
                    v.push_back(make_pair(a0,1));
                    v.push_back(make_pair(pi,-1));
                    v.push_back(make_pair(-pi,1));
                    v.push_back(make_pair(a1,-1));
                }
                else 
                {
                    v.push_back(make_pair(a0,1));
                    v.push_back(make_pair(a1,-1));
                }
            }
            sort(v.begin(),v.end());
            int cur=0;
            for (j=0;j<v.size();j++)
            {
                if (cur&&dblcmp(v[j].first-pre[cur]))
                {
                    ans[cur]+=areaarc(v[j].first-pre[cur],c[i].r);
                    ans[cur]+=0.5*point(c[i].p.x+c[i].r*cos(pre[cur]),c[i].p.y+c[i].r*sin(pre[cur])).det(point(c[i].p.x+c[i].r*cos(v[j].first),c[i].p.y+c[i].r*sin(v[j].first)));   
                }
                cur+=v[j].second;
                pre[cur]=v[j].first;
            }
        }
        for (i=1;i<=n;i++)
        {
            ans[i]-=ans[i+1];
        }
    }
};
struct halfplane:public line
{
    double angle;
    halfplane(){}
    //表示向量 a->b逆时针(左侧)的半平面
    halfplane(point _a,point _b)
    {
        a=_a;
        b=_b;
    }
    halfplane(line v)
    {
        a=v.a;
        b=v.b;
    }
    void calcangle()
    {
        angle=atan2(b.y-a.y,b.x-a.x);
    }
    bool operator<(const halfplane &b)const 
    {
        return angle<b.angle;
    }
};
struct halfplanes 
{
    int n;
    halfplane hp[maxp];
    point p[maxp];
    int que[maxp];
    int st,ed;
    void push(halfplane tmp)
    {
        hp[n++]=tmp;
    }
    void unique()
    {
        int m=1,i;
        for (i=1;i<n;i++)
        {
            if (dblcmp(hp[i].angle-hp[i-1].angle))hp[m++]=hp[i];
            else if (dblcmp(hp[m-1].b.sub(hp[m-1].a).det(hp[i].a.sub(hp[m-1].a))>0))hp[m-1]=hp[i];
        }
        n=m;
    }
    bool halfplaneinsert()
    {
        int i;
        for (i=0;i<n;i++)hp[i].calcangle();
        sort(hp,hp+n);
        unique();
        que[st=0]=0;
        que[ed=1]=1;
        p[1]=hp[0].crosspoint(hp[1]);
        for (i=2;i<n;i++)
        {
            while (st<ed&&dblcmp((hp[i].b.sub(hp[i].a).det(p[ed].sub(hp[i].a))))<0)ed--;
            while (st<ed&&dblcmp((hp[i].b.sub(hp[i].a).det(p[st+1].sub(hp[i].a))))<0)st++;
            que[++ed]=i;
            if (hp[i].parallel(hp[que[ed-1]]))return false;
            p[ed]=hp[i].crosspoint(hp[que[ed-1]]);
        }
        while (st<ed&&dblcmp(hp[que[st]].b.sub(hp[que[st]].a).det(p[ed].sub(hp[que[st]].a)))<0)ed--;
        while (st<ed&&dblcmp(hp[que[ed]].b.sub(hp[que[ed]].a).det(p[st+1].sub(hp[que[ed]].a)))<0)st++;
        if (st+1>=ed)return false;
        return true;
    }
    void getconvex(polygon &con)
    {
        p[st]=hp[que[st]].crosspoint(hp[que[ed]]);
        con.n=ed-st+1;
        int j=st,i=0;
        for (;j<=ed;i++,j++)
        {
            con.p[i]=p[j];
        }
    }
};
struct point3 
{
    double x,y,z;
    point3(){}
    point3(double _x,double _y,double _z):
    x(_x),y(_y),z(_z){};
    void input()
    {
        scanf("%lf%lf%lf",&x,&y,&z);
    }
    void output()
    {
        printf("%.2lf %.2lf %.2lf\n",x,y,z);
    }
    bool operator==(point3 a)
    {
        return dblcmp(a.x-x)==0&&dblcmp(a.y-y)==0&&dblcmp(a.z-z)==0;
    }
    bool operator<(point3 a)const
    {
        return dblcmp(a.x-x)==0?dblcmp(y-a.y)==0?dblcmp(z-a.z)<0:y<a.y:x<a.x;
    }
    double len()
    {
        return sqrt(len2());
    }
    double len2()
    {
        return x*x+y*y+z*z;
    }
    double distance(point3 p)
    {
        return sqrt((p.x-x)*(p.x-x)+(p.y-y)*(p.y-y)+(p.z-z)*(p.z-z));
    }
    point3 add(point3 p)
    {
        return point3(x+p.x,y+p.y,z+p.z);
    }
    point3 sub(point3 p)
    {
        return point3(x-p.x,y-p.y,z-p.z);
    }
    point3 mul(double d)
    {
        return point3(x*d,y*d,z*d);
    }
    point3 div(double d)
    {
        return point3(x/d,y/d,z/d);
    }
    double dot(point3 p)
    {
        return x*p.x+y*p.y+z*p.z;
    }
    point3 det(point3 p)
    {
        return point3(y*p.z-p.y*z,p.x*z-x*p.z,x*p.y-p.x*y);
    }
    double rad(point3 a,point3 b)
    {
        point3 p=(*this);
        return acos(a.sub(p).dot(b.sub(p))/(a.distance(p)*b.distance(p)));
    }
    point3 trunc(double r)
    {
        r/=len();
        return point3(x*r,y*r,z*r);
    }
};
struct line3 
{
    point3 a,b;
    line3(){}
    line3(point3 _a,point3 _b)
    {
        a=_a;
        b=_b;
    }
    bool operator==(line3 v)
    {
        return (a==v.a)&&(b==v.b);
    }
    void input()
    {
        a.input();
        b.input();
    }
    double length()
    {
        return a.distance(b);
    }
    bool pointonseg(point3 p)
    {
        return dblcmp(p.sub(a).det(p.sub(b)).len())==0&&dblcmp(a.sub(p).dot(b.sub(p)))<=0;
    }
    double dispointtoline(point3 p)
    {
        return b.sub(a).det(p.sub(a)).len()/a.distance(b);
    }
    double dispointtoseg(point3 p)
    {
        if (dblcmp(p.sub(b).dot(a.sub(b)))<0||dblcmp(p.sub(a).dot(b.sub(a)))<0)
        {
            return min(p.distance(a),p.distance(b));
        }
        return dispointtoline(p);
    }
    point3 lineprog(point3 p)
    {
        return a.add(b.sub(a).trunc(b.sub(a).dot(p.sub(a))/b.distance(a)));
    }   
    point3 rotate(point3 p,double ang)//p绕此向量逆时针arg角度
    {
        if (dblcmp((p.sub(a).det(p.sub(b)).len()))==0)return p;
        point3 f1=b.sub(a).det(p.sub(a));
        point3 f2=b.sub(a).det(f1);
        double len=fabs(a.sub(p).det(b.sub(p)).len()/a.distance(b));
        f1=f1.trunc(len);f2=f2.trunc(len);
        point3 h=p.add(f2);
        point3 pp=h.add(f1);
        return h.add((p.sub(h)).mul(cos(ang*1.0))).add((pp.sub(h)).mul(sin(ang*1.0)));
    }
};
struct plane
{
    point3 a,b,c,o;
    plane(){}
    plane(point3 _a,point3 _b,point3 _c)
    {
        a=_a;
        b=_b;
        c=_c;
        o=pvec();
    }
    plane(double _a,double _b,double _c,double _d)
    {
        //ax+by+cz+d=0
        o=point3(_a,_b,_c);
        if (dblcmp(_a)!=0)
        {
            a=point3((-_d-_c-_b)/_a,1,1);
        }
        else if (dblcmp(_b)!=0)
        {
            a=point3(1,(-_d-_c-_a)/_b,1);
        }
        else if (dblcmp(_c)!=0)
        {
            a=point3(1,1,(-_d-_a-_b)/_c);
        }
    }
    void input()
    {
        a.input();
        b.input();
        c.input();
        o=pvec();
    }
    point3 pvec()
    {
        return b.sub(a).det(c.sub(a));
    }
    bool pointonplane(point3 p)//点是否在平面上 
    {
        return dblcmp(p.sub(a).dot(o))==0;
    }
    //0 不在
    //1 在边界上
    //2 在内部 
    int pointontriangle(point3 p)//点是否在空间三角形abc上 
    {
        if (!pointonplane(p))return 0;
        double s=a.sub(b).det(c.sub(b)).len();
        double s1=p.sub(a).det(p.sub(b)).len();
        double s2=p.sub(a).det(p.sub(c)).len();
        double s3=p.sub(b).det(p.sub(c)).len();
        if (dblcmp(s-s1-s2-s3))return 0;
        if (dblcmp(s1)&&dblcmp(s2)&&dblcmp(s3))return 2;
        return 1;
    }
    //判断两平面关系  
    //0 相交
    //1 平行但不重合 
    //2 重合 
    bool relationplane(plane f)
    {
        if (dblcmp(o.det(f.o).len()))return 0;
        if (pointonplane(f.a))return 2;
        return 1;
    }
    double angleplane(plane f)//两平面夹角
    {
        return acos(o.dot(f.o)/(o.len()*f.o.len()));
    }
    double dispoint(point3 p)//点到平面距离
    {
        return fabs(p.sub(a).dot(o)/o.len());
    }
    point3 pttoplane(point3 p)//点到平面最近点
    {
        line3 u=line3(p,p.add(o));
        crossline(u,p);
        return p;
    }
    int crossline(line3 u,point3 &p)//平面和直线的交点 
    {
        double x=o.dot(u.b.sub(a));
        double y=o.dot(u.a.sub(a));
        double d=x-y;
        if (dblcmp(fabs(d))==0)return 0;
        p=u.a.mul(x).sub(u.b.mul(y)).div(d);
        return 1;
    }
    int crossplane(plane f,line3 &u)//平面和平面的交线 
    {
        point3 oo=o.det(f.o);
        point3 v=o.det(oo);
        double d=fabs(f.o.dot(v));
        if (dblcmp(d)==0)return 0;
        point3 q=a.add(v.mul(f.o.dot(f.a.sub(a))/d));
        u=line3(q,q.add(oo));
        return 1;
    }
};
//End Geometry

//Start MinCostFlow (yunkai version)
struct Edge{
    int u, v;
    long long cap, cost;
 
    Edge(int _u, int _v, long long _cap, long long _cost){
        u = _u; v = _v; cap = _cap; cost = _cost;
    }
};
 
struct MinCostFlow{
    int n, s, t;
    long long flow, cost;
    vector<vector<int> > graph;
    vector<Edge> e;
    vector<long long> dist, potential;
    vector<int> parent;
    bool negativeCost;
 
    MinCostFlow(int _n){
        // 0-based indexing
        n = _n;
        graph.assign(n, vector<int> ());
        negativeCost = false;
    }
 
    void addEdge(int u, int v, long long cap, long long cost, bool directed = true){
        if(cost < 0)
            negativeCost = true;
 
        graph[u].push_back(e.size());
        e.push_back(Edge(u, v, cap, cost));
 
        graph[v].push_back(e.size());
        e.push_back(Edge(v, u, 0, -cost));
 
        if(!directed)
            addEdge(v, u, cap, cost, true);
    }
 
    pair<long long, long long> getMinCostFlow(int _s, int _t){
        s = _s; t = _t;
        flow = 0, cost = 0;
 
        potential.assign(n, 0);
        if(negativeCost){
            // run Bellman-Ford to find starting potential
            dist.assign(n, 1LL<<62);
            for(int i = 0, relax = false; i < n && relax; i++, relax = false){
                for(int u = 0; u < n; u++){
                    for(int k = 0; k < graph[u].size(); k++){
                        int eIdx = graph[u][i];
                        int v = e[eIdx].v; ll cap = e[eIdx].cap, w = e[eIdx].cost;
 
                        if(dist[v] > dist[u] + w && cap > 0){
                            dist[v] = dist[u] + w;
                            relax = true;
            }   }   }   }
 
            for(int i = 0; i < n; i++){
                if(dist[i] < (1LL<<62)){
                    potential[i] = dist[i];
        }   }   }
 
        while(dijkstra()){
            flow += sendFlow(t, 1LL<<62);
        }
 
        return make_pair(flow, cost);
    }
 
    bool dijkstra(){
        parent.assign(n, -1);
        dist.assign(n, 1LL<<62);
        priority_queue<ii, vector<ii>, greater<ii> > pq;
 
        dist[s] = 0;
        pq.push(ii(0, s));
 
 
        while(!pq.empty()){
            int u = pq.top().second;
            long long d = pq.top().first;
            pq.pop();
 
            if(d != dist[u]) continue;
 
            for(int i = 0; i < graph[u].size(); i++){
                int eIdx = graph[u][i];
                int v = e[eIdx].v; ll cap = e[eIdx].cap;
                ll w = e[eIdx].cost + potential[u] - potential[v];
 
                if(dist[u] + w < dist[v] && cap > 0){
                    dist[v] = dist[u] + w;
                    parent[v] = eIdx;
 
                    pq.push(ii(dist[v], v));
        }   }   }
 
        // update potential
        for(int i = 0; i < n; i++){
            if(dist[i] < (1LL<<62))
                potential[i] += dist[i];
        }
 
        return dist[t] != (1LL<<62);
    }
 
    long long sendFlow(int v, long long curFlow){
        if(parent[v] == -1)
            return curFlow;
        int eIdx = parent[v];
        int u = e[eIdx].u; ll w = e[eIdx].cost;
 
        long long f = sendFlow(u, min(curFlow, e[eIdx].cap));
 
        cost += f*w;
        e[eIdx].cap -= f;
        e[eIdx^1].cap += f;
 
        return f;
    }
};
//End mincostflow

//Start mincostflowSPFA
struct Edge{
    int u, v;
    long long cap, cost;
 
    Edge(int _u, int _v, long long _cap, long long _cost){
        u = _u; v = _v; cap = _cap; cost = _cost;
    }
};
 
struct MinCostFlow{
    int n, s, t;
    long long flow, cost;
    vector<vector<int> > graph;
    vector<Edge> e;
    vector<long long> dist;
    vector<int> parent;
 
    MinCostFlow(int _n){
        // 0-based indexing
        n = _n;
        graph.assign(n, vector<int> ());
    }
 
    void addEdge(int u, int v, long long cap, long long cost, bool directed = true){
        graph[u].push_back(e.size());
        e.push_back(Edge(u, v, cap, cost));
 
        graph[v].push_back(e.size());
        e.push_back(Edge(v, u, 0, -cost));
 
        if(!directed)
            addEdge(v, u, cap, cost, true);
    }
 
    pair<long long, long long> getMinCostFlow(int _s, int _t){
        s = _s; t = _t;
        flow = 0, cost = 0;
 
        while(SPFA()){
            flow += sendFlow(t, 1LL<<62);
        }
 
        return make_pair(flow, cost);
    }
 
    // not sure about negative cycle
    bool SPFA(){
        parent.assign(n, -1);
        dist.assign(n, 1LL<<62);        dist[s] = 0;
        vector<int> queuetime(n, 0);    queuetime[s] = 1;
        vector<bool> inqueue(n, 0);     inqueue[s] = true;
        queue<int> q;                   q.push(s);
        bool negativecycle = false;
 
 
        while(!q.empty() && !negativecycle){
            int u = q.front(); q.pop(); inqueue[u] = false;
 
            for(int i = 0; i < graph[u].size(); i++){
                int eIdx = graph[u][i];
                int v = e[eIdx].v; ll w = e[eIdx].cost, cap = e[eIdx].cap;
 
                if(dist[u] + w < dist[v] && cap > 0){
                    dist[v] = dist[u] + w;
                    parent[v] = eIdx;
 
                    if(!inqueue[v]){
                        q.push(v);
                        queuetime[v]++;
                        inqueue[v] = true;
 
                        if(queuetime[v] == n+2){
                            negativecycle = true;
                            break;
                        }
                    }
                }
            }
        }
 
        return dist[t] != (1LL<<62);
    }
 
    long long sendFlow(int v, long long curFlow){
        if(parent[v] == -1)
            return curFlow;
        int eIdx = parent[v];
        int u = e[eIdx].u; ll w = e[eIdx].cost;
 
        long long f = sendFlow(u, min(curFlow, e[eIdx].cap));
 
        cost += f*w;
        e[eIdx].cap -= f;
        e[eIdx^1].cap += f;
 
        return f;
    }
};
//end mincostflowSPFA

//Start Z_{2} gausselim
struct gausselim
{
	ll cnt[61][2];
	int rank;
	ll cyc[61];
	ll tmp;
	void init()
	{
		for(int i = 0; i < 61; i++)
		{
			cyc[i] = cnt[i][0] = cnt[i][1] = 0;
		}
		rank = tmp = 0;
	}
	void addval(ll x)
	{
		for(int i = 0; i < 61; i++)
		{
			cnt[i][(x>>i)&1]++;
		}
	}
	void add(ll x)
	{
		tmp|=x;
		for(int i = 60; i >= 0; i--)
		{
			if(x&(1LL<<i))
			{
				if(cyc[i]==0)
				{
					cyc[i] = x;
					rank++;
					break;
				}
			}
			x = min(x, (x^cyc[i]));
		}	
	}
};
//End Z_{2} gausselim

//FFT
typedef complex<double> base;
const double PI = 3.14159265359;

struct FFT
{
	void fft(vector<base>& a, bool inv)
	{
		int n = int(a.size());
		if(n == 1) return ;
		vector<base> l(n/2), r(n/2);
		for(int i = 0, j = 0; i < n; i += 2, ++j)
		{
			l[j] = a[i];
			r[j] = a[i + 1];
		}
		//l contains the even polynomial, r contains the odd polynomial
		fft(l, inv); fft(r, inv);
		double ang = 2*PI/n;
		if(inv) ang*=-1;
		base w(1); 
		base rt(cos(ang), sin(ang));
		for(int i = 0; i < n/2; i++)
		{
			a[i] = l[i] + w*r[i];
			a[i+n/2] = l[i] - w*r[i];
			if(inv)
			{
				a[i] /= 2; a[i+n/2] /= 2;
			}
			w *= rt;
		}
	}

	void mult(vi &a, vi &b, vi &r)
	{
		int n = 1;
		while(n < max(a.size(), b.size())) n <<= 1;
		n <<= 1;
		vector<base> ffa; vector<base> ffb;
		base zero(0);
		ffa.assign(n, zero); ffb.assign(n, zero);
		for(int i=0;i<a.size();i++) ffa[i]=a[i];
		for(int i=0;i<b.size();i++) ffb[i]=b[i];
		fft(ffa, 0); fft(ffb, 0); //fft
		for(int i = 0; i < n; i++)
		{
			ffa[i] *= ffb[i]; //convolution
		}
		fft(ffa, 1); //inverse fft
		r.resize(n);
		for(int i = 0; i < n; i++)
		{
			r[i] = ll(ffa[i].real() + 0.5);
		}
	}
};
//End FFT

//FFT Pro
#define FOR(i, a, b) for (int i = (a); i < (b); ++i)
#define REP(i, n) FOR(i, 0, n)
namespace FFT2
{
  const int MAX = 1 << 20;
  const double PI = 3.14159265359;
  typedef ll value;
  typedef complex<double> comp;

  int N;
  comp omega[MAX];
  comp a1[MAX], a2[MAX];
  comp z1[MAX], z2[MAX];

  void fft(comp *a, comp *z, int m = N) {
    if (m == 1) {
      z[0] = a[0];
    } else {
      int s = N/m;
      m /= 2;

      fft(a, z, m);
      fft(a+s, z+m, m);

      REP(i, m) {
        comp c = omega[s*i] * z[m+i];
        z[m+i] = z[i] - c;
        z[i] += c;
      }
    }
  }

  void mult(value *a, value *b, value *c, int len) {
    N = 2*len;
    while (N & (N-1)) ++N;
    assert(N <= MAX);

    REP(i, N) a1[i] = 0;
    REP(i, N) a2[i] = 0;
    REP(i, len) a1[i] = a[i];
    REP(i, len) a2[i] = b[i];

    REP(i, N) omega[i] = polar(1.0, 2*M_PI/N*i);
    fft(a1, z1, N);
    fft(a2, z2, N);

    REP(i, N) omega[i] = comp(1, 0) / omega[i];
    REP(i, N) a1[i] = z1[i] * z2[i] / comp(N, 0);
    fft(a1, z1, N);

    REP(i, 2*len) c[i] = round(z1[i].real());
  }

  void mult_mod(ll *a, ll *b, ll *c, int len, int mod) {
    static ll a0[MAX], a1[MAX];
    static ll b0[MAX], b1[MAX];
    static ll c0[MAX], c1[MAX], c2[MAX];

    REP(i, len) a0[i] = a[i] & 0xFFFF;
    REP(i, len) a1[i] = a[i] >> 16;

    REP(i, len) b0[i] = b[i] & 0xFFFF;
    REP(i, len) b1[i] = b[i] >> 16;

    FFT2::mult(a0, b0, c0, len);
    FFT2::mult(a1, b1, c2, len);

    REP(i, len) a0[i] += a1[i];
    REP(i, len) b0[i] += b1[i];
    FFT2::mult(a0, b0, c1, len);
    REP(i, 2*len) c1[i] -= c0[i] + c2[i];

    REP(i, 2*len) c1[i] %= mod;
    REP(i, 2*len) c2[i] %= mod;
    REP(i, 2*len) c[i] = (c0[i] + (c1[i] << 16) + (c2[i] << 32)) % mod;
  }
}
//FFT Pro End

//Monotone Queue
template<class T> struct MaxQ {
  deque<T> D, Q;

  void push(T x) {
    while (!D.empty() && x > D.back()) D.pop_back(); // Change to `<` for MinQ
    D.push_back(x);
    Q.push_back(x);
  }

  void pop() {
    if (D.front() == Q.front()) D.pop_front();
    Q.pop_front();
  }

  T top()   { return D.front(); }
  T front() { return Q.front(); }
  T empty() { return Q.empty(); }
  T size()  { return Q.size();  }
};
//End Monotone Queue

//String Hash Start (taken from cgy4ever)
string T;
namespace H2 {
 
	long long mod = 1000000009LL;
 
	long long power(long long a, long long b)
	{
		long long ret = 1;
		while(b)
		{
			if(b&1)
				ret = (ret * a) % mod;
			a = (a * a) % mod;
			b /= 2;
		}
		return ret;
	}
 
 
	long long inv(long long x)
	{
		return power(x, mod - 2);
	}
 
	long long base = 10000019;
	long long val[100001];
	long long invPow[100001];
 
	long long getHash(int start, int len)
	{
		long long v = val[start + len] - val[start];
		v %= mod;
		if(v < 0) v += mod;
		v *= invPow[start];
		v %= mod;
		return v;
	}
 
 
 
	void prepare()
	{
		invPow[0] = 1;
		invPow[1] = inv(base);
		for(int i = 2; i <= 100000; i++)
			invPow[i] = (invPow[i-1] * invPow[1]) % mod;
		val[0] = 0;
		long long weight = 1;
		for(int i = 0; i < T.length(); i++)
		{
			val[i+1] = (val[i] + (long long)T[i] * weight) % mod;
			weight = (weight * base) % mod;
		}
	}
 
}
 
 
namespace H1 {
 
	long long mod = 1000000007LL;
 
	long long power(long long a, long long b)
	{
		long long ret = 1;
		while(b)
		{
			if(b&1)
				ret = (ret * a) % mod;
			a = (a * a) % mod;
			b /= 2;
		}
		return ret;
	}
 
 
	long long inv(long long x)
	{
		return power(x, mod - 2);
	}
 
	long long base = 22222223;
	long long val[100001];
	long long invPow[100001];
 
	long long getHash(int start, int len)
	{
		long long v = val[start + len] - val[start];
		v %= mod;
		if(v < 0) v += mod;
		v *= invPow[start];
		v %= mod;
		return v;
	}
 
 
 
	void prepare()
	{
		invPow[0] = 1;
		invPow[1] = inv(base);
		for(int i = 2; i <= 100000; i++)
			invPow[i] = (invPow[i-1] * invPow[1]) % mod;
		val[0] = 0;
		long long weight = 1;
		for(int i = 0; i < T.length(); i++)
		{
			val[i+1] = (val[i] + (long long)T[i] * weight) % mod;
			weight = (weight * base) % mod;
		}
	}
 
}
//End string hash

//Max Xor Query
class MaxXORQuery {

private:
    
    vector<vector<int> > jump;
    vector<int> newNode;
 
public:
 
    vector<int> numbers;
    
    MaxXORQuery () {
        jump.resize(1);
        jump[0].resize(2);
        jump[0][0] = jump[0][1] = 0;
        newNode.resize(2);
        newNode[0] = newNode[1] = 0;
    }
    
    void swapWith (MaxXORQuery& other) {
        jump.swap(other.jump);
        newNode.swap(other.newNode);
        numbers.swap(other.numbers);
    }
    
    void addNumber (int number) {
        int pos = 0;
        for(int i = 30; i + 1; i--) {
            int bit = ((number & (1 << i)) > 0);
            if (jump[pos][bit] == 0) {
                jump.push_back(newNode);
                jump[pos][bit] = (int)jump.size() - 1;
                pos = (int)jump.size() - 1;
            } else
                pos = jump[pos][bit];
        }
        numbers.push_back(number);
    }
    
    void clear () {
        jump.size();
        numbers.size();
    }
    
    int getMaxXORWith (int number) {
        int pos = 0;
        int result = 0;
        for(int i = 30; i + 1; i--) {
            int bit = ((number & (1 << i)) > 0);
            if (jump[pos][bit ^ 1] != 0) {
                pos = jump[pos][bit ^ 1];
                result += (1 << i);
            } else
                pos = jump[pos][bit];
        }
        return result;
    }
    
    size_t size () {
        return numbers.size();
    }
    
} mxQ[100001];
//End Max Xor Query

template <class T, int V>
class HeavyLight {
  int parent[V], heavy[V], depth[V];
  int root[V], treePos[V];
  SegmentTree<T> tree;

  template <class G>
  int dfs(const G& graph, int v) {
    int size = 1, maxSubtree = 0;
    for (int u : graph[v]) if (u != parent[v]) {
      parent[u] = v;
      depth[u] = depth[v] + 1;
      int subtree = dfs(graph, u);
      if (subtree > maxSubtree) heavy[v] = u, maxSubtree = subtree;
      size += subtree;
    }
    return size;
  }

  template <class BinaryOperation>
  void processPath(int u, int v, BinaryOperation op) {
    for (; root[u] != root[v]; v = parent[root[v]]) {
      if (depth[root[u]] > depth[root[v]]) swap(u, v);
      op(treePos[root[v]], treePos[v] + 1);
    }
    if (depth[u] > depth[v]) swap(u, v);
    op(treePos[u], treePos[v] + 1);
  }

public:
  template <class G>
  void init(const G& graph) {
    int n = graph.size();
    fill_n(heavy, n, -1);
    parent[0] = -1;
    depth[0] = 0;
    dfs(graph, 0);
    for (int i = 0, currentPos = 0; i < n; ++i)
      if (parent[i] == -1 || heavy[parent[i]] != i)
        for (int j = i; j != -1; j = heavy[j]) {
          root[j] = i;
          treePos[j] = currentPos++;
        }
    tree.init(n);
  }

  void set(int v, const T& value) {
    tree.set(treePos[v], value);
  }

  void modifyPath(int u, int v, const T& value) {
    processPath(u, v, [this, &value](int l, int r) { tree.modify(l, r, value); });
  }

  T queryPath(int u, int v) {
    T res = T();
    processPath(u, v, [this, &res](int l, int r) { res.add(tree.query(l, r)); });
    return res;
  }
};

//begin SCC
struct SCC
{
	const int INF = int(1e9);
	vector<vector<int> > vec;
	int index;
	vector<int> idx;
	vector<int> lowlink;
	vector<bool> onstack;
	stack<int> s;
	vector<int> sccidx;
	int scccnt;
	vi topo;
	
	//lower sccidx means appear later
	void init(int n)
	{
		idx.assign(n,-1);
		index = 0;
		onstack.assign(n,0);
		lowlink.assign(n,INF);
		while(!s.empty()) s.pop();
		sccidx.assign(n,-1);
		scccnt = 0;
		vec.clear();
		topo.clear();
		vec.resize(n);
	}
	
	void addedge(int u, int v) //u -> v
	{
		vec[u].pb(v);
	}
	
	void connect(int u)
	{
		idx[u] = index;
		lowlink[u] = index;
		index++;
		s.push(u);
		onstack[u] = true;
		for(int i = 0; i < vec[u].size(); i++)
		{
			int v = vec[u][i];
			if(idx[v] == -1)
			{
				connect(v);
				lowlink[u] = min(lowlink[u], lowlink[v]);
			}
			else if(onstack[v])
			{
				lowlink[u] = min(lowlink[u], idx[v]);
			}
		}
		if(lowlink[u] == idx[u])
		{
			while(1)
			{
				int v = s.top();
				s.pop();
				onstack[v] = false;
				sccidx[v] = scccnt;
				if(v == u) break;
			}
			scccnt++;
		}
	}
	
	void tarjan()
	{
		for(int i = 0; i < vec.size(); i++)
		{
			if(idx[i] == -1)
			{
				connect(i);
			}
		}
	}
	
	void toposort() //if graph is a DAG and i just want to toposort
	{
		tarjan();
		int n = vec.size();
		topo.resize(n);
		vector<ii> tmp;
		for(int i = 0; i < n; i++)
		{
			tmp.pb(mp(sccidx[i],i));
		}
		sort(tmp.begin(),tmp.end());
		reverse(tmp.begin(),tmp.end());
		for(int i = 0; i < n; i++)
		{
			topo[i]=tmp[i].se;
			if(i>0) assert(tmp[i].fi!=tmp[i-1].fi);
		}
	}
};
//end SCC

//begin Link-Cut Tree
template<class T> struct splnode {
  typedef splnode<T> node_t;

  splnode() : P(NULL), flip(0), pp(NULL) {
    C[0] = C[1] = NULL;
    fix();
  }

  node_t* P;
  node_t* C[2];

  int flip;
  node_t* pp;

  /* Fix the parent pointers of our children.  Additionally if we have any
   * extra data we're tracking (e.g. sum of subtree elements) now is the time to
   * update them (all of the children will already be up to date). */
  void fix() {
    if(C[0]) C[0]->P = this;
    if(C[1]) C[1]->P = this;
  }

  /* Push the flip bit down the tree. */
  void push_flip() {
    if(!flip) return;
    flip = 0;
    swap(C[0], C[1]);
    if(C[0]) C[0]->flip ^= 1;
    if(C[1]) C[1]->flip ^= 1;
  }

  /* Return the direction of this relative its parent. */
  int up() {
    return !P ? -1 : (P->C[0] == this ? 0 : 1);
  }

  /* Simple zig step in the 'c' direction when we've reached the root. */
  void zig(int c) {
    node_t* X = C[c];
    if(X->P = P) P->C[up()] = X;
    C[c] = X->C[1 - c];
    X->C[1 - c] = this;
    fix(); X->fix();
    if(P) P->fix();
    swap(pp, X->pp);
  }

  /* Zig zig in the 'c' direction both times. */
  void zigzig(int c) {
    node_t* X = C[c];
    node_t* Y = X->C[c];
    if(Y->P = P) P->C[up()] = Y;
    C[c] = X->C[1 - c];
    X->C[c] = Y->C[1 - c];
    Y->C[1 - c] = X;
    X->C[1 - c] = this;
    fix(); X->fix(); Y->fix();
    if(P) P->fix();
    swap(pp, Y->pp);
  }

  /* Zig zag first in the 'c' direction then in the '1-c' direciton. */
  void zigzag(int c) {
    node_t* X = C[c];
    node_t* Y = X->C[1 - c];
    if(Y->P = P) P->C[up()] = Y;
    C[c] = Y->C[1 - c];
    X->C[1 - c] = Y->C[c];
    Y->C[1 - c] = this;
    Y->C[c] = X;
    fix(); X->fix(); Y->fix();
    if(P) P->fix();
    swap(pp, Y->pp);
  }

  /* Splay this up to the root.  Always finishes without flip set. */
  node_t* splay() {
    for(push_flip(); P; ) {
      /* Reorganize flip bits so we can rotate as normal. */
      if(P->P) P->P->push_flip();
      P->push_flip();
      push_flip();

      int c1 = up();
      int c2 = P->up();
      if(c2 == -1) {
        P->zig(c1);
      } else if(c1 == c2) {
        P->P->zigzig(c1);
      } else {
        P->P->zigzag(c2);
      }
    }
    return this;
  }

  /* Return the max element of the subtree rooted at this. */
  node_t* last() {
    push_flip();
    return C[1] ? C[1]->last()  : splay();
  }

  /* Return the min element of the subtree rooted at this. */
  node_t* first() {
    push_flip();
    return C[0] ? C[0]->first() : splay();
  }
};


template<class T>
struct linkcut {
typedef splnode<T> node_t;

linkcut(int N) : node(N) {
}

void link(int u, int v) {
  make_root(v);
  node[v].pp = &node[u];
}

void cut(int u, int v) {
  make_root(u);
  node[v].splay();
  if(node[v].pp) {
    node[v].pp = NULL;
  } else {
    node[v].C[0]->P = NULL;
    node[v].C[0] = NULL;
    node[v].fix();
  }
}

bool connected(int u, int v) {
  node_t* nu = access(u)->first();
  node_t* nv = access(v)->first();
  return nu == nv;
}

/* Move u to root of represented tree. */
void make_root(int u) {
  access(u);
  node[u].splay();
  if(node[u].C[0]) {
    node[u].C[0]->P = NULL;
    node[u].C[0]->flip ^= 1;
    node[u].C[0]->pp = &node[u];

    node[u].C[0] = NULL;
    node[u].fix();
  }
}

/* Move u to root aux tree.  Return the root of the root aux tree. */
splnode<T>* access(int u) {
  node_t* x,* pp;
  for(x = node[u].splay(); x->pp; x = pp) {
    pp = x->pp->splay();
    x->pp = NULL;
    if(pp->C[1]) {
      pp->C[1]->P = NULL;
      pp->C[1]->pp = pp;
    }
    pp->C[1] = x;
    pp->fix();
  }
  return x;
}

vector<node_t> node;
};
//end Link-Cut Tree

//start Hopkraft Matching
const int MAXN1 = 50000;
const int MAXN2 = 50000;
const int MAXM = 150000;

int n1, n2, edges, last[MAXN1], pre[MAXM], head[MAXM];
int matching[MAXN2], dist[MAXN1], Q[MAXN1];
bool used[MAXN1], vis[MAXN1];

void init(int _n1, int _n2) 
{
    n1 = _n1;
    n2 = _n2;
    edges = 0;
    fill(last, last + n1, -1);
}

void addEdge(int u, int v) 
{
    head[edges] = v;
    pre[edges] = last[u];
    last[u] = edges++;
}

void bfs() 
{
    fill(dist, dist + n1, -1);
    int sizeQ = 0;
    for (int u = 0; u < n1; ++u) {
        if (!used[u]) {
            Q[sizeQ++] = u;
            dist[u] = 0;
        }
    }
    for (int i = 0; i < sizeQ; i++) {
        int u1 = Q[i];
        for (int e = last[u1]; e >= 0; e = pre[e]) {
            int u2 = matching[head[e]];
            if (u2 >= 0 && dist[u2] < 0) {
                dist[u2] = dist[u1] + 1;
                Q[sizeQ++] = u2;
            }
        }
    }
}

bool dfs(int u1) 
{
    vis[u1] = true;
    for (int e = last[u1]; e >= 0; e = pre[e]) {
        int v = head[e];
        int u2 = matching[v];
        if (u2 < 0 || ((!vis[u2] && dist[u2] == dist[u1] + 1) && dfs(u2))) {
            matching[v] = u1;
            used[u1] = true;
            return true;
        }
    }
    return false;
}

int maxMatching() 
{
    fill(used, used + n1, false);
    fill(matching, matching + n2, -1);
    for (int res = 0;;) {
        bfs();
        fill(vis, vis + n1, false);
        int f = 0;
        for (int u = 0; u < n1; ++u)
            if (!used[u] && dfs(u))
                ++f;
        if (!f)
            return res;
        res += f;
    }
}

const long long INFINITY = 1000000000000000000LL;
class ConvexHullDynamic {
	typedef long long coef_t;
	typedef long long coord_t;
	typedef long long val_t;

private:
	struct Line {
		coef_t a, b;
		double xLeft;

		enum Type {
			line, maxQuery, minQuery
		} type;
		coord_t val;

		explicit Line(coef_t aa = 0, coef_t bb = 0) :
				a(aa), b(bb), xLeft(-INFINITY), type(Type::line), val(0) {
		}
		val_t valueAt(coord_t x) const {
			return a * x + b;
		}
		friend bool areParallel(const Line& l1, const Line& l2) {
			return l1.a == l2.a;
		}
		friend double intersectX(const Line& l1, const Line& l2) {
			return areParallel(l1, l2) ?
					INFINITY : 1.0 * (l2.b - l1.b) / (l1.a - l2.a);
		}
		bool operator<(const Line& l2) const {
			if (l2.type == line)
				return this->a < l2.a;
			if (l2.type == maxQuery)
				return this->xLeft < l2.val;
			if (l2.type == minQuery)
				return this->xLeft > l2.val;

			return 0;
		}
	};

private:
	bool isMax;
	std::set<Line> hull;

private:
	bool hasPrev(std::set<Line>::iterator it) {
		return it != hull.begin();
	}
	bool hasNext(std::set<Line>::iterator it) {
		return it != hull.end() && std::next(it) != hull.end();
	}
	bool irrelevant(const Line& l1, const Line& l2, const Line& l3) {
		return intersectX(l1, l3) <= intersectX(l1, l2);
	}
	bool irrelevant(std::set<Line>::iterator it) {
		return hasPrev(it) && hasNext(it) && ((isMax && irrelevant(*std::prev(it), *it, *std::next(it)))
						|| (!isMax && irrelevant(*std::next(it), *it,
										*std::prev(it))));
	}

	std::set<Line>::iterator updateLeftBorder(std::set<Line>::iterator it) {
		if ((isMax && !hasPrev(it)) || (!isMax && !hasNext(it)))
			return it;

		double val = intersectX(*it, isMax ? *std::prev(it) : *std::next(it));
		Line buf(*it);
		it = hull.erase(it);
		buf.xLeft = val;
		it = hull.insert(it, buf);
		return it;
	}

public:
	ConvexHullDynamic() {
		isMax = true;
	}

	void addLine(coef_t a, coef_t b) {
		Line l3 = Line(a, b);
		auto it = hull.lower_bound(l3);

		if (it != hull.end() && areParallel(*it, l3)) {
			if ((isMax && it->b < b) || (!isMax && it->b > b))
				it = hull.erase(it);
			else
				return;
		}

		it = hull.insert(it, l3);
		if (irrelevant(it)) {
			hull.erase(it);
			return;
		}

		while (hasPrev(it) && irrelevant(std::prev(it)))
			hull.erase(std::prev(it));
		while (hasNext(it) && irrelevant(std::next(it)))
			hull.erase(std::next(it));

		it = updateLeftBorder(it);
		if (hasPrev(it))
			updateLeftBorder(std::prev(it));
		if (hasNext(it))
			updateLeftBorder(std::next(it));
	}
	
	val_t getBest(coord_t x) const {
		if (hull.size() == 0) {
			return -INFINITY;
		}
		Line q;
		q.val = x;
		q.type = isMax ? Line::Type::maxQuery : Line::Type::minQuery;

		auto bestLine = hull.lower_bound(q);
		if (isMax)
			--bestLine;
		return bestLine->valueAt(x);
	}
};

//Convex Hull Dynamic (for Open-book OI, since it's short)
const ll is_query = -(1LL<<62);
struct Line {
    ll m, b;
    mutable function<const Line*()> succ;
    bool operator<(const Line& rhs) const {
        if (rhs.b != is_query) return m < rhs.m;
        const Line* s = succ();
        if (!s) return 0;
        ll x = rhs.m;
        return 1.0L * b - s->b < 1.0L *(s->m - m) * x;
    }
};
struct ConvexHullDynamic : public multiset<Line> { // will maintain upper hull for maximum
    bool bad(iterator y) {
        auto z = next(y);
        if (y == begin()) {
            if (z == end()) return 0;
            return y->m == z->m && y->b <= z->b;
        }
        auto x = prev(y);
        if (z == end()) return y->m == x->m && y->b <= x->b;
        return (x->b - y->b)*1.0L*(z->m - y->m) >= (y->b - z->b)*1.0L*(y->m - x->m);
    }
    void insert_line(ll m, ll b) {
        auto y = insert({ m, b });
        y->succ = [=] { return next(y) == end() ? 0 : &*next(y); };
        if (bad(y)) { erase(y); return; }
        while (next(y) != end() && bad(next(y))) erase(next(y));
        while (y != begin() && bad(prev(y))) erase(prev(y));
    }
    ll eval(ll x) {
        auto l = *lower_bound((Line) { x, is_query });
        return l.m * x + l.b;
    }
};
//end Matching

template<unsigned mod>
class modulo {
private:
	unsigned x;
public:
	modulo() : x(0) {};
	modulo(unsigned x_) : x(x_) {};
	operator unsigned() { return x; }
	modulo operator==(const modulo& m) const { return x == m.x; }
	modulo operator!=(const modulo& m) const { return x != m.x; }
	modulo& operator+=(const modulo& m) { x = (x + m.x >= mod ? x + m.x - mod : x + m.x); return *this; }
	modulo& operator-=(const modulo& m) { x = (x < m.x ? x - m.x + mod : x - m.x); return *this; }
	modulo& operator*=(const modulo& m) { x = 1ULL * x * m.x % mod; return *this; }
	modulo operator+(const modulo& m) const { return modulo(*this) += m; }
	modulo operator-(const modulo& m) const { return modulo(*this) -= m; }
	modulo operator*(const modulo& m) const { return modulo(*this) *= m; }
};
 
// ------------ Matrix Functions ------------ //
typedef std::vector<modulo<998244353> > matrix_base;
typedef std::vector<matrix_base> matrix;
matrix mul(const matrix& a, const matrix& b) {
	assert(a[0].size() == b.size());
	matrix ret(a.size(), matrix_base(b[0].size(), 0));
	for (int i = 0; i < a.size(); i++) {
		for (int j = 0; j < b[0].size(); j++) {
			for (int k = 0; k < b.size(); k++) ret[i][j] += a[i][k] * b[k][j];
		}
	}
	return ret;
}
matrix unit(int n) {
	matrix ret(n, matrix_base(n, 0));
	for (int i = 0; i < n; i++) ret[i][i] = 1;
	return ret;
}
matrix power(const matrix& a, long long b) {
	assert(a.size() == a[0].size());
	matrix f = a, ret = unit(a.size());
	while (b) {
		if (b & 1) ret = mul(ret, f);
		f = mul(f, f);
		b >>= 1;
	}
	return ret;
}
 
// ------------ Modpower Algorithm ------------ //
inline int modpow(int a, int b, int m) {
	int ret = 1;
	while (b) {
		if (b & 1) ret = 1LL * ret * a % m;
		a = 1LL * a * a % m;
		b >>= 1;
	}
	return ret;
}
 
// ------------ Number Theoretic Transform ------------ //
inline static std::vector<int> FastModuloTransform(std::vector<int> v, int base, int root) {
	int n = v.size();
	for (int i = 0, j = 1; j < n - 1; j++) {
		for (int k = n >> 1; k >(i ^= k); k >>= 1);
		if (i < j) std::swap(v[i], v[j]);
	}
	for (int b = 1; b <= n / 2; b *= 2) {
		int x = modpow(root, (base - 1) / (b << 1), base);
		for (int i = 0; i < n; i += (b << 1)) {
			int p = 1;
			for (int j = i; j < i + b; j++) {
				int t1 = v[j], t2 = 1LL * v[j + b] * p % base;
				v[j] = t1 + t2; v[j] = (v[j] < base ? v[j] : v[j] - base);
				v[j + b] = t1 - t2 + base; v[j + b] = (v[j + b] < base ? v[j + b] : v[j + b] - base);
				p = 1LL * p * x % base;
			}
		}
	}
	return v;
}
inline static std::vector<int> FastConvolutionMod(std::vector<int> v1, std::vector<int> v2, int mod, int tr) {
	int n = v1.size() * 2; // v1 and v2 must be the same size!!
	v1.resize(n);
	v2.resize(n);
	v1 = FastModuloTransform(v1, mod, tr);
	v2 = FastModuloTransform(v2, mod, tr);
	for (int i = 0; i < n; i++) v1[i] = 1LL * v1[i] * v2[i] % mod;
	v1 = FastModuloTransform(v1, mod, modpow(tr, mod - 2, mod));
	int t = modpow(n, mod - 2, mod);
	for (int i = 0; i < n; i++) v1[i] = 1LL * v1[i] * t % mod;
	return v1;
}
 
// ------------ Lagrange Interpolation ------------ //
std::vector<int> lagrange_interpolation(std::vector<int> &v, int m) {
	int n = v.size() - 1;
	std::vector<int> inv(n + 2); inv[1] = 1;
	for (int i = 2; i <= n; i++) inv[i] = 1LL * inv[m % i] * (m - m / i) % m;
	std::vector<int> ret(n + 1);
	int q = 1;
	for (int i = 1; i <= n; i++) q = 1LL * q * inv[i] % m;
	if (n % 2 == 1) q = (m - q) % m;
	for (int i = 0; i <= n; i++) {
		ret[i] = 1LL * v[i] * q % m;
		q = 1LL * q * (m - n + i) % m * inv[i + 1] % m;
	}
	return ret;
}
int lagrange_function(int x, std::vector<int> &v, int m) {
	int n = v.size() - 1;
	int mul = 1;
	for (int i = 0; i <= n; i++) mul = 1LL * mul * (x - i + m) % m;
	int ret = 0;
	for (int i = 0; i <= n; i++) ret = (ret + 1LL * v[i] * modpow(x - i + m, m - 2, m)) % m;
	return 1LL * ret * mul % m;
}

class LazySegmentTree {
private:
	int size_;
	vector<long long> v, lazy;
	void update(int a, int b, long long x, int k, int l, int r) {
		push(k, l, r);
		if (r <= a || b <= l) return;
		if (a <= l && r <= b) {
			lazy[k] = x;
			push(k, l, r);
		}
		else {
			update(a, b, x, k * 2, l, (l + r) >> 1);
			update(a, b, x, k * 2 + 1, (l + r) >> 1, r);
			v[k] = merge(v[k * 2], v[k * 2 + 1]);
		}
	}
	long long query(int a, int b, int k, int l, int r) {
		push(k, l, r);
		if (r <= a || b <= l) return 0;
		if (a <= l && r <= b) return v[k];
		long long lc = query(a, b, k * 2, l, (l + r) >> 1);
		long long rc = query(a, b, k * 2 + 1, (l + r) >> 1, r);
		return merge(lc, rc);
	}
 
public:
	LazySegmentTree() : v(vector<long long>()), lazy(vector<long long>()) {};
	LazySegmentTree(int n) {
		for (size_ = 1; size_ < n;) size_ <<= 1;
		v.resize(size_ * 2);
		lazy.resize(size_ * 2);
	}
	inline void push(int k, int l, int r) {
		if (lazy[k] != 0) {
			v[k] += lazy[k] * (r - l);
			if (r - l > 1) {
				lazy[k * 2] += lazy[k];
				lazy[k * 2 + 1] += lazy[k];
			}
			lazy[k] = 0;
		}
	}
	inline long long merge(long long x, long long y) {
		return x + y;
	}
	inline void update(int l, int r, long long x) {
		update(l, r, x, 1, 0, size_);
	}
	inline long long query(int l, int r) {
		return query(l, r, 1, 0, size_);
	}
};
//See more http://codeforces.com/blog/entry/22072


#include <cstdio>
#include <cassert>
#include <vector>

using namespace std;

typedef long long ll;
typedef pair<int, int> Pii;

#define FOR(i,n) for(int i = 0; i < (n); i++)
#define sz(c) ((int)(c).size())
#define ten(x) ((int)1e##x)

template<class T> T extgcd(T a, T b, T& x, T& y) { for (T u = y = 1, v = x = 0; a;) { T q = b / a; swap(x -= q * u, u); swap(y -= q * v, v); swap(b -= q * a, a); } return b; }
template<class T> T mod_inv(T a, T m) { T x, y; extgcd(a, m, x, y); return (m + x % m) % m; }
ll mod_pow(ll a, ll n, ll mod) { ll ret = 1; ll p = a % mod; while (n) { if (n & 1) ret = ret * p % mod; p = p * p % mod; n >>= 1; } return ret; }

template<int mod, int primitive_root>
class NTT {
public:
	int get_mod() const { return mod; }
	void _ntt(vector<ll>& a, int sign) {
		const int n = sz(a);
		assert((n ^ (n&-n)) == 0); //n = 2^k

		const int g = 3; //g is primitive root of mod
		int h = (int)mod_pow(g, (mod - 1) / n, mod); // h^n = 1
		if (sign == -1) h = (int)mod_inv(h, mod); //h = h^-1 % mod

		//bit reverse
		int i = 0;
		for (int j = 1; j < n - 1; ++j) {
			for (int k = n >> 1; k >(i ^= k); k >>= 1);
			if (j < i) swap(a[i], a[j]);
		}

		for (int m = 1; m < n; m *= 2) {
			const int m2 = 2 * m;
			const ll base = mod_pow(h, n / m2, mod);
			ll w = 1;
			FOR(x, m) {
				for (int s = x; s < n; s += m2) {
					ll u = a[s];
					ll d = a[s + m] * w % mod;
					a[s] = u + d;
					if (a[s] >= mod) a[s] -= mod;
					a[s + m] = u - d;
					if (a[s + m] < 0) a[s + m] += mod;
				}
				w = w * base % mod;
			}
		}

		for (auto& x : a) if (x < 0) x += mod;
	}
	void ntt(vector<ll>& input) {
		_ntt(input, 1);
	}
	void intt(vector<ll>& input) {
		_ntt(input, -1);
		const int n_inv = mod_inv(sz(input), mod);
		for (auto& x : input) x = x * n_inv % mod;
	}

	// 畳み込み演算を行う
	vector<ll> convolution(const vector<ll>& a, const vector<ll>& b){
		int ntt_size = 1;
		while (ntt_size < sz(a) + sz(b)) ntt_size *= 2;

		vector<ll> _a = a, _b = b;
		_a.resize(ntt_size); _b.resize(ntt_size);

		ntt(_a);
		ntt(_b);

		FOR(i, ntt_size){
			(_a[i] *= _b[i]) %= mod;
		}

		intt(_a);
		return _a;
	}
};

ll garner(vector<Pii> mr, int mod){
	mr.emplace_back(mod, 0);

	vector<ll> coffs(sz(mr), 1);
	vector<ll> constants(sz(mr), 0);
	FOR(i, sz(mr) - 1){
		// coffs[i] * v + constants[i] == mr[i].second (mod mr[i].first) を解く
		ll v = (mr[i].second - constants[i]) * mod_inv<ll>(coffs[i], mr[i].first) % mr[i].first;
		if (v < 0) v += mr[i].first;

		for (int j = i + 1; j < sz(mr); j++) {
			(constants[j] += coffs[j] * v) %= mr[j].first;
			(coffs[j] *= mr[i].first) %= mr[j].first;
		}
	}

	return constants[sz(mr) - 1];
}

typedef NTT<167772161, 3> NTT_1;
typedef NTT<469762049, 3> NTT_2;
typedef NTT<1224736769, 3> NTT_3;

//任意のmodで畳み込み演算 O(n log n)
vector<ll> int32mod_convolution(vector<ll> a, vector<ll> b,int mod){
	for (auto& x : a) x %= mod;
	for (auto& x : b) x %= mod;
	NTT_1 ntt1; NTT_2 ntt2; NTT_3 ntt3;
	auto x = ntt1.convolution(a, b);
	auto y = ntt2.convolution(a, b);
	auto z = ntt3.convolution(a, b);

	vector<ll> ret(sz(x));
	vector<Pii> mr(3);
	FOR(i, sz(x)){
		mr[0].first = ntt1.get_mod(), mr[0].second = (int)x[i];
		mr[1].first = ntt2.get_mod(), mr[1].second = (int)y[i];
		mr[2].first = ntt3.get_mod(), mr[2].second = (int)z[i];
		ret[i] = garner(mr, mod);
	}

	return ret;
}

// garnerのアルゴリズムを直書きしたversion，速い
vector<ll> fast_int32mod_convolution(vector<ll> a, vector<ll> b,int mod){
	for (auto& x : a) x %= mod;
	for (auto& x : b) x %= mod;
	
	NTT_1 ntt1; NTT_2 ntt2; NTT_3 ntt3;
	assert(ntt1.get_mod() < ntt2.get_mod() && ntt2.get_mod() < ntt3.get_mod());
	auto x = ntt1.convolution(a, b);
	auto y = ntt2.convolution(a, b);
	auto z = ntt3.convolution(a, b);

	// garnerのアルゴリズムを極力高速化した
	const ll m1 = ntt1.get_mod(), m2 = ntt2.get_mod(), m3 = ntt3.get_mod();
	const ll m1_inv_m2 = mod_inv<ll>(m1, m2);
	const ll m12_inv_m3 = mod_inv<ll>(m1 * m2, m3);
	const ll m12_mod = m1 * m2 % mod;
	vector<ll> ret(sz(x));
	FOR(i, sz(x)){
		ll v1 = (y[i] - x[i]) *  m1_inv_m2 % m2;
		if (v1 < 0) v1 += m2;
		ll v2 = (z[i] - (x[i] + m1 * v1) % m3) * m12_inv_m3 % m3;
		if (v2 < 0) v2 += m3;
		ll constants3 = (x[i] + m1 * v1 + m12_mod * v2) % mod;
		if (constants3 < 0) constants3 += mod;
		ret[i] = constants3;
	}

	return ret;
}

//2^23より大きく，primitive rootに3を持つもの
// const int mods[] = { 1224736769, 469762049, 167772161, 595591169, 645922817, 897581057, 998244353 };

void ntt_test() {
	NTT_1 ntt;

	vector<ll> v;
	FOR(i, 16) v.push_back(10 + i);

	auto v2 = v;
	ntt.ntt(v2);

	auto v3 = v2;
	ntt.intt(v3);

	assert(v == v3);
}

void comvolution_test() {
	NTT_1 ntt1;

	vector<ll> v = { 1, 2, 3 };
	vector<ll> u = { 4, 5, 6 };

	auto vu = ntt1.convolution(v, u);
	vector<ll> vu2 = { 1 * 4, 1 * 5 + 2 * 4, 1 * 6 + 2 * 5 + 3 * 4, 2 * 6 + 3 * 5, 3 * 6, 0, 0, 0 };
	assert(vu == vu2);
}

void int32mod_convolution_test(){
	vector<ll> x , y;
	FOR(i, 10) x.push_back(ten(8) + i);
	y = x;

	auto z = int32mod_convolution(x, y, ten(9) + 7);
	z.resize(sz(x) + sz(y) - 1);
	vector<ll> z2 = { 
		930000007, 60000000, 390000001, 920000004,
		650000003, 580000006, 710000014, 40000021,
		570000042, 300000064, 370000109, 240000144,
		910000175, 380000187, 650000193, 720000185,
		590000162, 260000123, 730000074 };
	assert(z == z2);
}

void test(){
	ntt_test();
	comvolution_test();
	int32mod_convolution_test();
}

//Edmond's Algorithm (MST on directed graph)
template<typename T> //http://sunmoon-template.blogspot.my/2017/02/minimum-arborescence-zhuliu.html
struct edmond{
	static const int MAXN=110,MAXM=10005;
	struct node{
		int u,v;
		T w,tag;
		node *l,*r;
		node(int u=0,int v=0,T w=0):u(u),v(v),w(w),tag(0),l(0),r(0){}
		void down(){
			w+=tag;
			if(l)l->tag+=tag;
			if(r)r->tag+=tag;
			tag=0;
		}
	}mem[MAXM];//靜態記憶體 
	node *pq[MAXN*2],*E[MAXN*2];
	int st[MAXN*2],id[MAXN*2],m;
	void init(int n){
		for(int i=1;i<=n;++i){
			pq[i]=E[i]=0;
			st[i]=id[i]=i;
		}m=0;
	}
	node *merge(node *a,node *b){//skew heap
		if(!a||!b)return a?a:b;
		a->down(),b->down();
		if(b->w<a->w)return merge(b,a);
		swap(a->l,a->r);
		a->l=merge(b,a->l);
		return a;
	}
	void add_edge(int u,int v,T w){
		if(u!=v)pq[v]=merge(pq[v],&(mem[m++]=node(u,v,w)));
	}
	int find(int x,int *st){
		return st[x]==x?x:st[x]=find(st[x],st);
	}
	T build(int root,int n){
		T ans=0;int N=n,all=n;
		for(int i=1;i<=N;++i){
			if(i==root||!pq[i])continue;
			while(pq[i]){
				pq[i]->down(),E[i]=pq[i];
				pq[i]=merge(pq[i]->l,pq[i]->r);
				if(find(E[i]->u,id)!=find(i,id))break;
			}
			if(find(E[i]->u,id)==find(i,id))continue;
			ans+=E[i]->w;
			if(find(E[i]->u,st)==find(i,st)){
				if(pq[i])pq[i]->tag-=E[i]->w;
				pq[++N]=pq[i],id[N]=N;
				for(int u=find(E[i]->u,id);u!=i;u=find(E[u]->u,id)){
					if(pq[u])pq[u]->tag-=E[u]->w;
					id[find(u,id)]=N;
					pq[N]=merge(pq[N],pq[u]);
				}
				st[N]=find(i,st);
				id[find(i,id)]=N;
			}else st[find(i,st)]=find(E[i]->u,st),--all;
		}
		return all==1?ans:-INT_MAX;//圖不連通就無解 
	}
};
//End Edmond

//Start Determinant (mod P)
ll calc(void)
{
    int i,j,k;

    bool neg = false;
    
    for(j = 0; j < n; j++)
    {
        for(i = j; i < n; i++) if(a[i][j] != 0) break;
        if(i == n) return 0;
        if(i != j)
        {
            neg = !neg;
            for(int k = 0; k < n; k++) swap(a[i][k],a[j][k]);
        }
        for(i = j + 1; i < n; i++)
        {
            ll coef = ((P - a[i][j])*modpow(a[j][j],P-2)) % P;
            for(k = j; k < n; k++) 
            {
				a[i][k] = (a[i][k] + a[j][k] * coef) % P;
			}
        }
    }
    ll ans = (neg ? (P - 1) : 1);
	for(i = 0; i < n; i++) ans = ans * a[i][i] % P;
	if(ans<0) ans+=P;
    return ans;
}

//Wavelet Tree
struct wavelet_tree
{
	int lo, hi;
	wavelet_tree *l, *r;
	vi b;	 
	//nos are in range [x,y]
	//array indices are [from, to), from >= 1
	wavelet_tree(int *from, int *to, int x, int y)
	{
		lo = x, hi = y;
		if(lo == hi or from >= to) return;
		int mid = (lo+hi)/2;
		auto f = [mid](int x)
		{
			return x <= mid;
		};
		b.reserve(to-from+1);
		b.pb(0);
		for(auto it = from; it != to; it++)
		b.pb(b.back() + f(*it));
		//see how lambda function is used here
		auto pivot = stable_partition(from, to, f);
		l = new wavelet_tree(from, pivot, lo, mid);
		r = new wavelet_tree(pivot, to, mid+1, hi);
	}
	//kth smallest element in [l, r]
	int kth(int l, int r, int k)
	{
		if(l > r) return 0;
		if(lo == hi) return lo;
		int inLeft = b[r] - b[l-1];
		int lb = b[l-1]; //amt of nos in first (l-1) nos that go in left
		int rb = b[r]; //amt of nos in first (r) nos that go in left
		if(k <= inLeft) return this->l->kth(lb+1, rb , k);
		return this->r->kth(l-lb, r-rb, k-inLeft);
	}
	 
	//count of nos in [l, r] Less than or equal to k
	int LTE(int l, int r, int k)
	{
		if(l > r or k < lo) return 0;
		if(hi <= k) return r - l + 1;
		int lb = b[l-1], rb = b[r];
		return this->l->LTE(lb+1, rb, k) + this->r->LTE(l-lb, r-rb, k);
	}
	 
	//count of nos in [l, r] equal to k
	int count(int l, int r, int k) 
	{
		if(l > r or k < lo or k > hi) return 0;
		if(lo == hi) return r - l + 1;
		int lb = b[l-1], rb = b[r], mid = (lo+hi)/2;
		if(k <= mid) return this->l->count(lb+1, rb, k);
		return this->r->count(l-lb, r-rb, k);
	}
	~wavelet_tree()
	{
		delete l;
		delete r;
	}
};

wavelet_tree T(a+1, a+n+1, 1, MAX);
cin >> q;
while(q--)
{
	int x;
	cin >> x;
	cin >> l >> r >> k;
	if(x == 0)
	{
		//kth smallest
		cout << "Kth smallest: ";
		cout << T.kth(l, r, k) << endl;
	}
	if(x == 1)
	{
		//less than or equal to K
		cout << "LTE: ";
		cout << T.LTE(l, r, k) << endl;
	}
	if(x == 2)
	{
		//count occurence of K in [l, r]
		cout << "Occurence of K: ";
		cout << T.count(l, r, k) << endl;
	}
}
//End Wavelet


//Combi Class
struct Combi
{
	vector<int> fact;
	vector<int> ifact;
	vector<int> inv;
	vector<int> pow2;
	const int MOD = (1e9 + 7);
	int add(int a, int b)
	{
		a+=b;
		while(a>=MOD) a-=MOD;
		return a;
	}
	void radd(int &a, int b)
	{
		a=add(a,b); 
	}
	int mult(int a, int b)
	{
		return (a*1LL*b)%MOD;
	}
	void rmult(int &a, int b)
	{
		a=mult(a,b);
	}
	int modpow(int a, int b)
	{
		int r=1;
		while(b)
		{
			if(b&1) r=mult(r,a);
			a=mult(a,a);
			b>>=1;
		}
		return r;
	}
	int choose(int a, int b)
	{
		if(a<b) return 0;
		if(b==0) return 1;
		if(a==b) return 1;
		return mult(fact[a],mult(ifact[b],ifact[a-b]));
	}
	int inverse(int a)
	{
		return modpow(a,MOD-2);
	}
	void init(int _n)
	{
		fact.clear(); ifact.clear(); inv.clear(); pow2.clear();
		fact.resize(_n+1);
		ifact.resize(_n+1);
		inv.resize(_n+1);
		pow2.resize(_n+1);
		pow2[0]=1;
		ifact[0]=1;
		fact[0]=1;
		for(int i=1;i<=_n;i++)
		{
			pow2[i]=add(pow2[i-1],pow2[i-1]);
			fact[i]=mult(fact[i-1],i);
			//ifact[i]=mult(ifact[i-1],inv[i]);
		}
		ifact[_n] = inverse(fact[_n]);
		for(int i=_n-1;i>=1;i--)
		{
		    ifact[i] = mult(ifact[i + 1], i + 1);
		}
		for(int i=1;i<=_n;i++)
		{
		    inv[i] = mult(fact[i-1],ifact[i]);
		}
	}
};


//Bridge Tree
vi tree[N]; // The bridge edge tree formed from the given graph
vi graph[N];int U[M],V[M];  //edge list representation of the graph. 
bool isbridge[M]; // if i'th edge is a bridge edge or not 
int visited[N];int arr[N],T; //supporting arrays
int cmpno;
queue<int> Q[N];

int adj(int u,int e){
    return U[e]==u?V[e]:U[e];
}
int dfs0(int u,int edge)    //marks all the bridges
{
    visited[u]=1;
    arr[u]=T++;
    int dbe = arr[u];
    for(int i=0;i<(int)graph[u].size();i++)
    {
        int e = graph[u][i];
        int w = adj(u,e);
        if(!visited[w])
            dbe = min(dbe,dfs0(w,e));
        else if(e!=edge)
            dbe = min(dbe,arr[w]);
    }
    if(dbe == arr[u] && edge!=-1)
        isbridge[edge]=true;
    return dbe;
}
 
void dfs1(int v) //Builds the tree with each edge a bridge from original graph
{
    int currcmp = cmpno;    // current component no.
    Q[currcmp].push(v);    // A different queue for each component, coz   during bfs we shall go to another component (step of dfs) and then come   back to this one and continue our bfs
    visited[v]=1;
    while(!Q[currcmp].empty())    //bfs. Exploring all nodes of this  component
    {
        int u = Q[currcmp].front();    
        Q[currcmp].pop();    
        for(int i=0;i<(int)graph[u].size();i++)
        {
            int e = graph[u][i];
            int w = adj(u,e);
            if(visited[w])continue;
            //if the edge under consideration is bridge and
            //other side is not yet explored, go there (step of dfs)
            if(isbridge[e])
            {
                cmpno++;
                tree[currcmp].push_back(cmpno);
                tree[cmpno].push_back(currcmp);
                dfs1(w);
            }
            else     //else continue with our bfs
            {
                Q[currcmp].push(w);
                visited[w]=1;
            }
        }
    }
}
//End Bridge Tree

//Block Cut Tree
struct graph
{
	int n;
	vector<vector<int>> adj;
 
	graph(int n) : n(n), adj(n) {}
 
	void add_edge(int u, int v)
	{
		adj[u].push_back(v);
		adj[v].push_back(u);
	}
 
	int add_node()
	{
		adj.push_back({});
		return n++;
	}
 
	vector<int>& operator[](int u) { return adj[u]; }
};
 
vector<vector<int>> biconnected_components(graph &adj)
{
	int n = adj.n;
 
	vector<int> num(n), low(n), art(n), stk;
	vector<vector<int>> comps;
 
	function<void(int, int, int&)> dfs = [&](int u, int p, int &t)
	{
		num[u] = low[u] = ++t;
		stk.push_back(u);
 
		for (int v : adj[u]) if (v != p)
		{
			if (!num[v])
			{
				dfs(v, u, t);
				low[u] = min(low[u], low[v]);
 
				if (low[v] >= num[u])
				{
					art[u] = (num[u] > 1 || num[v] > 2);
 
					comps.push_back({u});
					while (comps.back().back() != v)
						comps.back().push_back(stk.back()), stk.pop_back();
				}
			}
			else low[u] = min(low[u], num[v]);
		}
	};
 
	for (int u = 0, t; u < n; ++u)
		if (!num[u]) dfs(u, -1, t = 0);
 
	// build the block cut tree
	function<graph()> build_tree = [&]()
	{
		graph tree(0);
		vector<int> id(n);
 
		for (int u = 0; u < n; ++u)
			if (art[u]) id[u] = tree.add_node();
 
		for (auto &comp : comps)
		{
			int node = tree.add_node();
			for (int u : comp)
				if (!art[u]) id[u] = node;
				else tree.add_edge(node, id[u]);
		}
 
		return tree;
	};
 
	return comps;
}
//End Block Cut Tree

//Palindromic Tree
const int maxn = 1e6+ 1, sigma = 26;
int len[maxn], link[maxn], to[maxn][sigma];
int slink[maxn], diff[maxn], series_ans[maxn];
int sz, last, n;
char s[maxn];
 
void init()
{
    s[n++] = -1;
    link[0] = 1;
    len[1] = -1;
    sz = 2;
}
 
int get_link(int v)
{
    while(s[n - len[v] - 2] != s[n - 1]) v = link[v];
    return v;
}
 
void add_letter(char c)
{
    s[n++] = c -= 'a';
    last = get_link(last);
    if(!to[last][c])
    {
        len[sz] = len[last] + 2;
        link[sz] = to[get_link(link[last])][c];
        diff[sz] = len[sz] - len[link[sz]];
        if(diff[sz] == diff[link[sz]])
            slink[sz] = slink[link[sz]];
        else
            slink[sz] = link[sz];
        to[last][c] = sz++;
    }
    last = to[last][c];
}

int main()
{
	ios_base::sync_with_stdio(0); cin.tie(0);
	string s; cin>>s;
	string s2 = s;
	int n=s.length();
	string t;
	for(int i=0;i<n/2;i++)
	{
		t+=s[i];
		t+=s[n-1-i];
	}
	//build pal tre for t
	init();
    int ans[n + 1];
    memset(ans, 0, sizeof(ans));
    ans[0] = 1;
    for(int i = 1; i <= n; i++)
    {
        add_letter(t[i - 1]);
        for(int v = last; len[v] > 0; v = slink[v])
        {
            series_ans[v] = ans[i - (len[slink[v]] + diff[v])];
            if(diff[v] == diff[link[v]])
                series_ans[v] = add(series_ans[v], series_ans[link[v]]);
            ans[i] = add(ans[i], series_ans[v]);
        }
        if(i&1) ans[i]=0;
    }
    cout<<ans[n]<<'\n';
}
//End Palindromic Tree

//Z Algorithm
int L = 0, R = 0;
for (int i = 1; i < n; i++) {
  if (i > R) {
    L = R = i;
    while (R < n && s[R-L] == s[R]) R++;
    z[i] = R-L; R--;
  } else {
    int k = i-L;
    if (z[k] < R-i+1) z[i] = z[k];
    else {
      L = i;
      while (R < n && s[R-L] == s[R]) R++;
      z[i] = R-L; R--;
    }
  }
}
//End Z Algorithm

//KMP Algorithm
vector<int> prefix_function (string Z) 
{
    int n = (int) Z.length();
    vector<int> F (n);
    F[0]=0;
    for (int i=1; i<n; ++i) 
    {
        int j = F[i-1];
        while (j > 0 && Z[i] != Z[j])
		{
            j = F[j-1];
        }
        if (Z[i] == Z[j])  ++j;
        F[i] = j;
    }
    return F;
}
//End KMP Algorithm

//Real HLD
void dfs_sz(int v = 0)
{
    sz[v] = 1;
    for(auto &u: g[v])
    {
        dfs_sz(u);
        sz[v] += sz[u];
        if(sz[u] > sz[g[v][0]])
            swap(u, g[v][0]);
    }
}

void dfs_hld(int v = 0)
{
    in[v] = t++;
    rin[in[v]] = v;
    for(auto u: g[v])
    {
        nxt[u] = (u == g[v][0] ? nxt[v] : u);
        dfs_hld(u);
    }
    out[v] = t;
}
//End Real HLD

//Begin Aho Corasick
const int MAXN = 404, MOD = 1e9 + 7, sigma = 26;
 
int term[MAXN], len[MAXN], to[MAXN][sigma], link[MAXN], sz = 1;
void add_str(string s)
{
    int cur = 0;
    for(auto c: s)
    {
        if(!to[cur][c - 'a'])
        {
            to[cur][c - 'a'] = sz++;
            len[to[cur][c - 'a']] = len[cur] + 1;
        }
        cur = to[cur][c - 'a'];
    }
    term[cur] = cur; 
}
 
void push_links()
{
    int que[sz];
    int st = 0, fi = 1;
    que[0] = 0;
    while(st < fi)
    {
        int V = que[st++];
        int U = link[V];
        if(!term[V]) term[V] = term[U];
        for(int c = 0; c < sigma; c++)
        {
            if(to[V][c])
            {
                link[to[V][c]] = V ? to[U][c] : 0;
                que[fi++] = to[V][c];
            }
            else
            {
                to[V][c] = to[U][c];
            }
		}	
    }
}
//End Aho Corasick

//Begin Link Cut Tree
struct monoid {
	using type = int;
	static type id() { return 0; }
	static type op(const type& l, const type & r) { return l + r; }
};

template <typename M>
class lct_node {
	using T = typename M::type;
	lct_node *l, *r, *p;
	bool rev;
	T val, all;

	int pos() {
		if (p && p->l == this) return -1;
		if (p && p->r == this) return 1;
		return 0;
	}
	void update() {
		all = M::op(l ? l->all : M::id(), M::op(val, r ? r->all : M::id()));
	}
	void push() {
		if (pos()) p->push();
		if (rev) {
			swap(l, r);
			if (l) l->rev ^= true;
			if (r) r->rev ^= true;
			rev = false;
		}
	}
	void rot() {
		lct_node *par = p;
		lct_node *mid;
		if (p->l == this) {
			mid = r;
			r = par;
			par->l = mid;
		}
		else {
			mid = l;
			l = par;
			par->r = mid;
		}
		if (mid) mid->p = par;
		p = par->p;
		par->p = this;
		if (p && p->l == par) p->l = this;
		if (p && p->r == par) p->r = this;
		par->update();
		update();
	}
	void splay() {
		push();
		while (pos()) {
			int st = pos() * p->pos();
			if (!st) rot();
			else if (st == 1) p->rot(), rot();
			else rot(), rot();
		}
	}

public:
	lct_node(int v = 0) : l(nullptr), r(nullptr), p(nullptr), rev(false), val(v), all(v) {}
	void expose() {
		for (lct_node *x = this, *y = nullptr; x; y = x, x = x->p) x->splay(), x->r = y, x->update();
		splay();
	}
	void link(lct_node *x) {
		x->expose();
		expose();
		p = x;
	}
	void cut() {
		expose();
		l->p = nullptr;
		l = nullptr;
		update();
	}
	void evert() {
		expose();
		rev = true;
	}
	T get() const {
		return val;
	}
	void update(T v) {
		expose();
		val = v;
		update();
	}
}
//End Link Cut Tree

//Begin Edmond Blossom
#define MAX 100
#define undef -2
#define empty -1
#define noEdge 0
#define unmatched 1
#define matched 2
#define forward 0
#define reverse 0

                    //Labels are the key to this implementation of the algorithm.
struct Label {      //An even label in a vertex means there's an alternating path
       int even;    //of even length starting from the root node that ends on the
       int odd[2];  //vertex. To find this path, the backtrace() function is called,
};                  //constructing the path by following the content of the labels.
                    //Odd labels are similar, the only difference is that base nodes
                    //of blossoms inside other blossoms may have two. More on this later.


struct elem {            //This is the element of the queue of labels to be analyzed by
       int vertex,type;  //the augmentMatching() procedure. Each element contains the vertex
};                       //where the label is and its type, odd or even.


int g[MAX][MAX];         //The graph, as an adjacency matrix.

                         //blossom[i] contains the base node of the blossom the vertex i
int blossom[MAX];        //is in. This, together with labels eliminates the need to
                         //contract the graph.

                              //The path arrays are where the backtrace() routine will
int path[2][MAX],endPath[2];  //store the paths it finds. Only two paths need to be
                              //stored. endPath[p] denotes the end of path[p].

bool match[MAX];  //An array of flags. match[i] stores if vertex i is in the matching.

                  //label[i] contains the label assigned to vertex i. It may be undefined,
Label label[MAX]; //empty (meaning the node is a root) and a node might have even and odd
                  //labels at the same time, which is the case for nonbase nodes of blossoms

elem queue[2*MAX];         //The queue is necessary for efficiently scanning all labels.
int queueFront,queueBack;  //A label is enqueued when assigned and dequeued after scanned.

void initGraph(int n){
     for (int i=0; i<n; i++)
         for (int j=0; j<n; j++) g[i][j]=noEdge;
}

int readGraph(){
     int n,e,a,b;
     scanf(" %d %d",&n,&e);      //The graph is read and its edges are unmatched by default.
     initGraph(n);               //Since C++ arrays are 0..n-1 and input 1..n , subtractions 
     for (int i=0; i<e; i++){    //are made for better memory usage.
         scanf(" %d %d",&a,&b);
         if (a!=b)
            g[a-1][b-1]=g[b-1][a-1]=unmatched;
     }
     return n;
}

void initAlg(int n){             //Initializes all data structures for the augmentMatching()
     queueFront=queueBack=0;     //function begin. At the start, all labels are undefined,
     for (int i=0; i<n; i++){    //the queue is empty and a node alone is its own blossom.
         blossom[i]=i;
         label[i].even=label[i].odd[0]=label[i].odd[1]=undef;
     }
}

void backtrace (int vert, int pathNum, int stop, int parity, int direction){
     if (vert==stop) return;           //pathNum is the number of the path to store
     else if (parity==0){              //vert and parity determine the label to be read.
        if (direction==reverse){
           backtrace(label[vert].even,pathNum,stop,(parity+1)%2,reverse);
           path[pathNum][endPath[pathNum]++]=vert;
        }                             //forward means the vertices called first enter
        else if (direction==forward){ //the path first, reverse is the opposite.
             path[pathNum][endPath[pathNum]++]=vert;
             backtrace(label[vert].even,pathNum,stop,(parity+1)%2,forward);
        }
     }
     /*
       stop is the stopping condition for the recursion.
       Recursion is necessary because of the possible dual odd labels.
       having empty at stop means the recursion will only stop after
       the whole tree has been climbed. If assigned to a vertex, it'll stop
       once it's reached.
     */
     else if (parity==1 && label[vert].odd[1]==undef){
        if (direction==reverse){
           backtrace(label[vert].odd[0],pathNum,stop,(parity+1)%2,reverse);
           path[pathNum][endPath[pathNum]++]=vert;
        }
        else if (direction==forward){
             path[pathNum][endPath[pathNum]++]=vert;
             backtrace(label[vert].odd[0],pathNum,stop,(parity+1)%2,forward);
        }
     }
     /*
       Dual odd labels are interpreted as follows:
       There exists an odd length alternating path starting from the root to this
       vertex. To find this path, backtrace from odd[0] to the top of the tree and
       from odd[1] to the vertex itself. This, put in the right order, will
       constitute said path.
     */
     else if (parity==1 && label[vert].odd[1]!=undef){
          if (direction==reverse){
             backtrace(label[vert].odd[0],pathNum,empty,(parity+1)%2,reverse);
             backtrace(label[vert].odd[1],pathNum,vert,(parity+1)%2,forward);
             path[pathNum][endPath[pathNum]++]=vert;
          }
          else if (direction==forward){
               backtrace(label[vert].odd[1],pathNum,vert,(parity+1)%2,reverse);
               backtrace(label[vert].odd[0],pathNum,empty,(parity+1)%2,forward);
               path[pathNum][endPath[pathNum]++]=vert;
          }
     }
}

void enqueue (int vert, int t){
     elem tmp;               //Enqueues labels for scanning.
     tmp.vertex=vert;        //No label that's dequeued during the execution
     tmp.type=t;             //of augmentMatching() goes back to the queue.
     queue[queueBack++]=tmp; //Thus, circular arrays are unnecessary.
}

void newBlossom (int a, int b){     //newBlossom() will be called after the paths are evaluated.
     int i,base,innerBlossom,innerBase;
     for (i=0; path[0][i]==path[1][i]; i++);   //Find the lowest common ancestor of a and b
     i--;                                      //it will be used to represent the blossom.
     base=blossom[path[0][i]];                 //Unless it's already contained in another...
                                               //In this case, all will be put in the older one.
     for (int j=i; j<endPath[0]; j++) blossom[path[0][j]]=base;
     for (int j=i+1; j<endPath[1]; j++) blossom[path[1][j]]=base; //Set all nodes to this
     for (int p=0; p<2; p++){                                     //new blossom.
        for (int j=i+1; j<endPath[p]-1; j++){
            if (label[path[p][j]].even==undef){        //Now, new labels will be applied
               label[path[p][j]].even=path[p][j+1];    //to indicate the existence of even
               enqueue(path[p][j],0);                  //and odd length paths.
            }
            else if (label[path[p][j]].odd[0]==undef && label[path[p][j+1]].even==undef){
                 label[path[p][j]].odd[0]=path[p][j+1];
                 enqueue(path[p][j],1);                 //Labels will only be put if the vertex
            }                                           //doesn't have one.
            
            else if (label[path[p][j]].odd[0]==undef && label[path[p][j+1]].even!=undef){
                 /*
                   If a vertex doesn't have an odd label, but the next one in the path
                   has an even label, it means that the current vertex is the base node
                   of a previous blossom and the next one is contained within it.
                   The standard labeling procedure will fail in this case. This is fixed
                   by going to the last node in the path inside this inner blossom and using
                   it to apply the dual label.
                   Refer to backtrace() to know how the path will be built.
                 */
                 innerBlossom=blossom[path[p][j]];
                 innerBase=j;
                 for (; blossom[j]==innerBlossom && j<endPath[p]-1; j++);
                 j--;
                 label[path[p][innerBase]].odd[0]=path[p][j+1];
                 label[path[p][innerBase]].odd[1]=path[p][j];
                 enqueue(path[p][innerBase],1);
            }
        }
     }
     if (g[a][b]==unmatched){           //All nodes have received labels, except
        if (label[a].odd[0]==undef){    //the ones that called the function in
           label[a].odd[0]=b;           //the first place. It's possible to
           enqueue(a,1);                //find out how to label them by
        }                               //analyzing if they're in the matching.
        if (label[b].odd[0]==undef){
           label[b].odd[0]=a;
           enqueue(b,1);
        }                               
     }
     else if (g[a][b]==matched){
          if (label[a].even==undef){
             label[a].even=b;
             enqueue(a,0);
          }
          if (label[b].even==undef){
             label[b].even=a;
             enqueue(b,0);
          }
     }
}

void augmentPath (){           //An augmenting path has been found in the matching
     int a,b;                  //and is contained in the path arrays.
     for (int p=0; p<2; p++){
         for (int i=0; i<endPath[p]-1; i++){
             a=path[p][i];             //Because of labeling, this path is already
             b=path[p][i+1];           //lifted and can be augmented by simple
             if (g[a][b]==unmatched)   //changing of the matching status.
                g[a][b]=g[b][a]=matched;
             else if (g[a][b]==matched)
                  g[a][b]=g[b][a]=unmatched;
         }
     }
     a=path[0][endPath[0]-1];
     b=path[1][endPath[1]-1];
     if (g[a][b]==unmatched) g[a][b]=g[b][a]=matched;
     else if (g[a][b]==matched) g[a][b]=g[b][a]=unmatched;
     //After this, a and b are included in the matching.
     match[path[0][0]]=match[path[1][0]]=true;
}

bool augmentMatching (int n){  //The main analyzing function, with the
     int node,nodeLabel;       //goal of finding augmenting paths or
     initAlg(n);               //concluding that the matching is maximum.
     for (int i=0; i<n; i++) if (!match[i]){
         label[i].even=empty;
         enqueue(i,0);          //Initialize the queue with the exposed vertices,
     }                          //making them the roots in the forest.
     
     while (queueFront<queueBack){
         node=queue[queueFront].vertex;
         nodeLabel=queue[queueFront].type;
         if (nodeLabel==0){
            for (int i=0; i<n; i++) if (g[node][i]==unmatched){
                if (blossom[node]==blossom[i]);
                //Do nothing. Edges inside the same blossom have no meaning.
                else if (label[i].even!=undef){
                     /*
                       The tree has reached a vertex with a label.
                       The parity of this label indicates that an odd length
                       alternating path has been found. If this path is between
                       roots, we have an augmenting path, else there's an
                       alternating cycle, a blossom.
                     */
                     endPath[0]=endPath[1]=0;
                     backtrace(node,0,empty,0,reverse);
                     backtrace(i,1,empty,0,reverse);
                     //Call the backtracing function to find out.
                     if (path[0][0]==path[1][0]) newBlossom(node,i);
                     /*
                       If the same root node is reached, a blossom was found.
                       Start the labelling procedure to create pseudo-contraction.
                     */
                     else {
                          augmentPath();
                          return true;
                          /*
                            If the roots are different, we have an augmenting path.
                            Improve the matching by augmenting this path.
                            Now some labels might make no sense, stop the function,
                            returning that it was successful in improving.
                          */
                     }
                }
                else if (label[i].even==undef && label[i].odd[0]==undef){
                     //If an unseen vertex is found, report the existing path
                     //by labeling it accordingly.
                     label[i].odd[0]=node;
                     enqueue(i,1);
                }
            }
         }
         else if (nodeLabel==1){ //Similar to above.
            for (int i=0; i<n; i++) if (g[node][i]==matched){
                if (blossom[node]==blossom[i]);
                else if (label[i].odd[0]!=undef){
                     endPath[0]=endPath[1]=0;
                     backtrace(node,0,empty,1,reverse);
                     backtrace(i,1,empty,1,reverse);
                     if (path[0][0]==path[1][0]) newBlossom(node,i);
                     else {
                          augmentPath();
                          return true;
                     }
                }
                else if (label[i].even==undef && label[i].odd[0]==undef){
                     label[i].even=node;
                     enqueue(i,0);
                }
            }
         }
         /*
           The scanning of this label is complete, dequeue it and
           keep going to the next one.
         */
         queueFront++;
     }
     /*
       If the function reaches this point, the queue is empty, all
       labels have been scanned. The algorithm couldn't find an augmenting
       path. Therefore, it concludes the matching is maximum.
     */
     return false;
}

void findMaximumMatching (int n){
     //Initialize it with the empty matching.
     for (int i=0; i<n; i++) match[i]=false;
     //Run augmentMatching(), it'll keep improving the matching.
     //Eventually, it will no longer find a path and break the loop,
     //at this point, the current matching is maximum.
     while (augmentMatching(n));
}

int main(){
    int n;
    n=readGraph();
    findMaximumMatching(n);
    for (int i=0; i<n; i++){
        for (int j=i+1; j<n; j++) if (g[i][j]==matched)
            printf("%d %d\n",i+1,j+1);
    }
    return 0;
}
//End Edmond Blossom

//Max Weight Matching
#define DIST(e) (lab[e.u]+lab[e.v]-g[e.u][e.v].w*2)
using namespace std;
typedef long long ll;
const int N=1023,INF=1e9;
struct Edge
{
	int u,v,w;
} g[N][N];
int n,m,n_x,lab[N],match[N],slack[N],st[N],pa[N],flower_from[N][N],S[N],vis[N];
vector<int> flower[N];
deque<int> q;
void update_slack(int u,int x)
{
	if(!slack[x]||DIST(g[u][x])<DIST(g[slack[x]][x]))slack[x]=u;
}
void set_slack(int x)
{
	slack[x]=0;
	for(int u=1; u<=n; ++u)
		if(g[u][x].w>0&&st[u]!=x&&S[st[u]]==0)update_slack(u,x);
}
void q_push(int x)
{
	if(x<=n)return q.push_back(x);
	for(int i=0; i<flower[x].size(); i++)q_push(flower[x][i]);
}
void set_st(int x,int b)
{
	st[x]=b;
	if(x<=n)return;
	for(int i=0; i<flower[x].size(); ++i)set_st(flower[x][i],b);
}
int get_pr(int b,int xr)
{
	int pr=find(flower[b].begin(),flower[b].end(),xr)-flower[b].begin();
	if(pr%2==1) //檢查他在前一層圖是奇點還是偶點
	{
		reverse(flower[b].begin()+1,flower[b].end());
		return (int)flower[b].size()-pr;
	}
	else return pr;
}
void set_match(int u,int v)
{
	match[u]=g[u][v].v;
	if(u<=n)return;
	Edge e=g[u][v];
	int xr=flower_from[u][e.u],pr=get_pr(u,xr);
	for(int i=0; i<pr; ++i)set_match(flower[u][i],flower[u][i^1]);
	set_match(xr,v);
	rotate(flower[u].begin(),flower[u].begin()+pr,flower[u].end());
}
void augment(int u,int v)
{
	int xnv=st[match[u]];
	set_match(u,v);
	if(!xnv)return;
	set_match(xnv,st[pa[xnv]]);
	augment(st[pa[xnv]],xnv);
}
int get_lca(int u,int v)
{
	static int t=0;
	for(++t; u||v; swap(u,v))
	{
		if(u==0)continue;
		if(vis[u]==t)return u;
		vis[u]=t;//這種方法可以不用清空v陣列
		u=st[match[u]];
		if(u)u=st[pa[u]];
	}
	return 0;
}
void add_blossom(int u,int lca,int v)
{
	int b=n+1;
	while(b<=n_x&&st[b])++b;
	if(b>n_x)++n_x;
	lab[b]=0,S[b]=0;
	match[b]=match[lca];
	flower[b].clear();
	flower[b].push_back(lca);
	for(int x=u,y; x!=lca; x=st[pa[y]])
		flower[b].push_back(x),flower[b].push_back(y=st[match[x]]),q_push(y);
	reverse(flower[b].begin()+1,flower[b].end());
	for(int x=v,y; x!=lca; x=st[pa[y]])
		flower[b].push_back(x),flower[b].push_back(y=st[match[x]]),q_push(y);
	set_st(b,b);
	for(int x=1; x<=n_x; ++x)g[b][x].w=g[x][b].w=0;
	for(int x=1; x<=n; ++x)flower_from[b][x]=0;
	for(int i=0; i<flower[b].size(); ++i)
	{
		int xs=flower[b][i];
		for(int x=1; x<=n_x; ++x)
			if(g[b][x].w==0||DIST(g[xs][x])<DIST(g[b][x]))
				g[b][x]=g[xs][x],g[x][b]=g[x][xs];
		for(int x=1; x<=n; ++x)
			if(flower_from[xs][x])flower_from[b][x]=xs;
	}
	set_slack(b);
}
void expand_blossom(int b)  // S[b] == 1
{
	for(int i=0; i<flower[b].size(); ++i)
		set_st(flower[b][i],flower[b][i]);
	int xr=flower_from[b][g[b][pa[b]].u],pr=get_pr(b,xr);
	for(int i=0; i<pr; i+=2)
	{
		int xs=flower[b][i],xns=flower[b][i+1];
		pa[xs]=g[xns][xs].u;
		S[xs]=1,S[xns]=0;
		slack[xs]=0,set_slack(xns);
		q_push(xns);
	}
	S[xr]=1,pa[xr]=pa[b];
	for(int i=pr+1; i<flower[b].size(); ++i)
	{
		int xs=flower[b][i];
		S[xs]=-1,set_slack(xs);
	}
	st[b]=0;
}
bool on_found_Edge(const Edge &e)
{
	int u=st[e.u],v=st[e.v];
	if(S[v]==-1)
	{
		pa[v]=e.u,S[v]=1;
		int nu=st[match[v]];
		slack[v]=slack[nu]=0;
		S[nu]=0,q_push(nu);
	}
	else if(S[v]==0)
	{
		int lca=get_lca(u,v);
		if(!lca)return augment(u,v),augment(v,u),1;
		else add_blossom(u,lca,v);
	}
	return 0;
}
bool matching()
{
	fill(S,S+n_x+1,-1),fill(slack,slack+n_x+1,0);
	q.clear();
	for(int x=1; x<=n_x; ++x)
		if(st[x]==x&&!match[x])pa[x]=0,S[x]=0,q_push(x);
	if(q.empty())return 0;
	for(;;)
	{
		while(q.size())
		{
			int u=q.front();
			q.pop_front();
			if(S[st[u]]==1)continue;
			for(int v=1; v<=n; ++v)
				if(g[u][v].w>0&&st[u]!=st[v])
				{
					if(DIST(g[u][v])==0)
					{
						if(on_found_Edge(g[u][v]))return 1;
					}
					else update_slack(u,st[v]);
				}
		}
		int d=INF;
		for(int b=n+1; b<=n_x; ++b)
			if(st[b]==b&&S[b]==1)d=min(d,lab[b]/2);
		for(int x=1; x<=n_x; ++x)
			if(st[x]==x&&slack[x])
			{
				if(S[x]==-1)d=min(d,DIST(g[slack[x]][x]));
				else if(S[x]==0)d=min(d,DIST(g[slack[x]][x])/2);
			}
		for(int u=1; u<=n; ++u)
		{
			if(S[st[u]]==0)
			{
				if(lab[u]<=d)return 0;
				lab[u]-=d;
			}
			else if(S[st[u]]==1)lab[u]+=d;
		}
		for(int b=n+1; b<=n_x; ++b)
			if(st[b]==b)
			{
				if(S[st[b]]==0)lab[b]+=d*2;
				else if(S[st[b]]==1)lab[b]-=d*2;
			}
		q.clear();
		for(int x=1; x<=n_x; ++x)
			if(st[x]==x&&slack[x]&&st[slack[x]]!=x&&DIST(g[slack[x]][x])==0)
				if(on_found_Edge(g[slack[x]][x]))return 1;
		for(int b=n+1; b<=n_x; ++b)
			if(st[b]==b&&S[b]==1&&lab[b]==0)expand_blossom(b);
	}
	return 0;
}
pair<ll,int> weight_blossom()
{
	fill(match,match+n+1,0);
	n_x=n;
	int n_matches=0;
	ll tot_weight=0;
	for(int u=0; u<=n; ++u)st[u]=u,flower[u].clear();
	int w_max=0;
	for(int u=1; u<=n; ++u)
		for(int v=1; v<=n; ++v)
		{
			flower_from[u][v]=(u==v?u:0);
			w_max=max(w_max,g[u][v].w);
		}
	for(int u=1; u<=n; ++u)lab[u]=w_max;
	while(matching())++n_matches;
	for(int u=1; u<=n; ++u)
		if(match[u]&&match[u]<u)
			tot_weight+=g[u][match[u]].w;
	return make_pair(tot_weight,n_matches);
}
//End Max Weight Matching

//Linear Recurrence
#define SZ 233333
const int MOD=1e9+7; //or any prime
ll qp(ll a,ll b)
{
	ll x=1; a%=MOD;
	while(b)
	{
		if(b&1) x=x*a%MOD;
		a=a*a%MOD; b>>=1;
	}
	return x;
}
namespace linear_seq {
inline vector<int> BM(vector<int> x)
{
	//ls: (shortest) relation sequence (after filling zeroes) so far
	//cur: current relation sequence
	vector<int> ls,cur;
	//lf: the position of ls (t')
	//ld: delta of ls (v')
	int lf,ld;
	for(int i=0;i<int(x.size());++i)
	{
		ll t=0;
		//evaluate at position i
		for(int j=0;j<int(cur.size());++j)
			t=(t+x[i-j-1]*(ll)cur[j])%MOD;
		if((t-x[i])%MOD==0) continue; //good so far
		//first non-zero position
		if(!cur.size())
		{
			cur.resize(i+1);
			lf=i; ld=(t-x[i])%MOD;
			continue;
		}
		//cur=cur-c/ld*(x[i]-t)
		ll k=-(x[i]-t)*qp(ld,MOD-2)%MOD/*1/ld*/;
		vector<int> c(i-lf-1); //add zeroes in front
		c.pb(k);
		for(int j=0;j<int(ls.size());++j)
			c.pb(-ls[j]*k%MOD);
		if(c.size()<cur.size()) c.resize(cur.size());
		for(int j=0;j<int(cur.size());++j)
			c[j]=(c[j]+cur[j])%MOD;
		//if cur is better than ls, change ls to cur
		if(i-lf+(int)ls.size()>=(int)cur.size())
			ls=cur,lf=i,ld=(t-x[i])%MOD;
		cur=c;
	}
	for(int i=0;i<int(cur.size());++i)
		cur[i]=(cur[i]%MOD+MOD)%MOD;
	return cur;
}
int m; //length of recurrence
//a: first terms
//h: relation
ll a[SZ],h[SZ],t_[SZ],s[SZ],t[SZ];
//calculate p*q mod f
inline void mull(ll*p,ll*q)
{
	for(int i=0;i<m+m;++i) t_[i]=0;
	for(int i=0;i<m;++i) if(p[i])
		for(int j=0;j<m;++j)
			t_[i+j]=(t_[i+j]+p[i]*q[j])%MOD;
	for(int i=m+m-1;i>=m;--i) if(t_[i])
		//miuns t_[i]x^{i-m}(x^m-\sum_{j=0}^{m-1} x^{m-j-1}h_j)
		for(int j=m-1;~j;--j)
			t_[i-j-1]=(t_[i-j-1]+t_[i]*h[j])%MOD;
	for(int i=0;i<m;++i) p[i]=t_[i];
}
inline ll calc(ll K)
{
	for(int i=m;~i;--i)
		s[i]=t[i]=0;
	//init
	s[0]=1; if(m!=1) t[1]=1; else t[0]=h[0];
	//binary-exponentiation
	while(K)
	{
		if(K&1) mull(s,t);
		mull(t,t); K>>=1;
	}
	ll su=0;
	for(int i=0;i<m;++i) su=(su+s[i]*a[i])%MOD;
	return (su%MOD+MOD)%MOD;
}
inline int work(vector<int> x,ll n)
{
	if(n<int(x.size())) return x[n];
	vector<int> v=BM(x); m=v.size(); if(!m) return 0;
	for(int i=0;i<m;++i) h[i]=v[i],a[i]=x[i];
	return calc(n);
}
}
using linear_seq::work;
int main()
{
	cout<<work({1,1,2,3,5,8,13,21},10)<<"\n";
}
//End Linear Recurrence

//Begin Manachar
vector<int> pal_array(string s)
{
    int n = s.size();
    s = "@" + s + "$";
    vector<int> len(n + 1);
    int l = 1, r = 1;
    for(int i = 1; i <= n; i++)
    {
        len[i] = min(r - i, len[l + (r - i)]);
        while(s[i - len[i]] == s[i + len[i]])
            len[i]++;
        if(i + len[i] > r)
        {
            l = i - len[i];
            r = i + len[i];
        }
    }
    len.erase(begin(len));
    return len;
}
// calculates half-length of maximum odd palindrome with center in i
//"In case of even palindromes I suggest to use the same code with the string s1#s2#... #sn" - adamant
//End Manachar

//Polynomial
namespace algebra {
	const int inf = 1e9;
	const int magic = 500; // threshold for sizes to run the naive algo
	
	namespace fft {
		const int maxn = 1 << 18;

		typedef double ftype;
		typedef complex<ftype> point;

		point w[maxn];
		const ftype pi = acos(-1);
		bool initiated = 0;
		void init() {
			if(!initiated) {
				for(int i = 1; i < maxn; i *= 2) {
					for(int j = 0; j < i; j++) {
						w[i + j] = polar(ftype(1), pi * j / i);
					}
				}
				initiated = 1;
			}
		}
		template<typename T>
		void fft(T *in, point *out, int n, int k = 1) {
			if(n == 1) {
				*out = *in;
			} else {
				n /= 2;
				fft(in, out, n, 2 * k);
				fft(in + k, out + n, n, 2 * k);
				for(int i = 0; i < n; i++) {
					auto t = out[i + n] * w[i + n];
					out[i + n] = out[i] - t;
					out[i] += t;
				}
			}
		}
		
		template<typename T>
		void mul_slow(vector<T> &a, const vector<T> &b) {
			vector<T> res(a.size() + b.size() - 1);
			for(size_t i = 0; i < a.size(); i++) {
				for(size_t j = 0; j < b.size(); j++) {
					res[i + j] += a[i] * b[j];
				}
			}
			a = res;
		}
		
		
		template<typename T>
		void mul(vector<T> &a, const vector<T> &b) {
			if(min(a.size(), b.size()) < magic) {
				mul_slow(a, b);
				return;
			}
			init();
			static const int shift = 15, mask = (1 << shift) - 1;
			size_t n = a.size() + b.size() - 1;
			while(__builtin_popcount(n) != 1) {
				n++;
			}
			a.resize(n);
			static point A[maxn], B[maxn];
			static point C[maxn], D[maxn];
			for(size_t i = 0; i < n; i++) {
				A[i] = point(a[i] & mask, a[i] >> shift);
				if(i < b.size()) {
					B[i] = point(b[i] & mask, b[i] >> shift);
				} else {
					B[i] = 0;
				}
			}
			fft(A, C, n); fft(B, D, n);
			for(size_t i = 0; i < n; i++) {
				point c0 = C[i] + conj(C[(n - i) % n]);
				point c1 = C[i] - conj(C[(n - i) % n]);
				point d0 = D[i] + conj(D[(n - i) % n]);
				point d1 = D[i] - conj(D[(n - i) % n]);
				A[i] = c0 * d0 - point(0, 1) * c1 * d1;
				B[i] = c0 * d1 + d0 * c1;
			}
			fft(A, C, n); fft(B, D, n);
			reverse(C + 1, C + n);
			reverse(D + 1, D + n);
			int t = 4 * n;
			for(size_t i = 0; i < n; i++) {
				int64_t A0 = llround(real(C[i]) / t);
				T A1 = llround(imag(D[i]) / t);
				T A2 = llround(imag(C[i]) / t);
				a[i] = A0 + (A1 << shift) + (A2 << 2 * shift);
			}
			return;
		}
	}
	template<typename T>
	T bpow(T x, size_t n) {
		return n ? n % 2 ? x * bpow(x, n - 1) : bpow(x * x, n / 2) : T(1);
	}
	template<typename T>
	T bpow(T x, size_t n, T m) {
		return n ? n % 2 ? x * bpow(x, n - 1, m) % m : bpow(x * x % m, n / 2, m) : T(1);
	}
	template<typename T>
	T gcd(const T &a, const T &b) {
		return b == T(0) ? a : gcd(b, a % b);
	}
	template<typename T>
	T nCr(T n, int r) { // runs in O(r)
		T res(1);
		for(int i = 0; i < r; i++) {
			res *= (n - T(i));
			res /= (i + 1);
		}
		return res;
	}

	template<int m>
	struct modular {
		int64_t r;
		modular() : r(0) {}
		modular(int64_t rr) : r(rr) {if(abs(r) >= m) r %= m; if(r < 0) r += m;}
		modular inv() const {return bpow(*this, m - 2);}
		modular operator * (const modular &t) const {return (r * t.r) % m;}
		modular operator / (const modular &t) const {return *this * t.inv();}
		modular operator += (const modular &t) {r += t.r; if(r >= m) r -= m; return *this;}
		modular operator -= (const modular &t) {r -= t.r; if(r < 0) r += m; return *this;}
		modular operator + (const modular &t) const {return modular(*this) += t;}
		modular operator - (const modular &t) const {return modular(*this) -= t;}
		modular operator *= (const modular &t) {return *this = *this * t;}
		modular operator /= (const modular &t) {return *this = *this / t;}
		
		bool operator == (const modular &t) const {return r == t.r;}
		bool operator != (const modular &t) const {return r != t.r;}
		
		operator int64_t() const {return r;}
	};
	template<int T>
	istream& operator >> (istream &in, modular<T> &x) {
		return in >> x.r;
	}
	
	
	template<typename T>
	struct poly {
		vector<T> a;
		
		void normalize() { // get rid of leading zeroes
			while(!a.empty() && a.back() == T(0)) {
				a.pop_back();
			}
		}
		
		poly(){}
		poly(T a0) : a{a0}{normalize();}
		poly(vector<T> t) : a(t){normalize();}
		
		poly operator += (const poly &t) {
			a.resize(max(a.size(), t.a.size()));
			for(size_t i = 0; i < t.a.size(); i++) {
				a[i] += t.a[i];
			}
			normalize();
			return *this;
		}
		poly operator -= (const poly &t) {
			a.resize(max(a.size(), t.a.size()));
			for(size_t i = 0; i < t.a.size(); i++) {
				a[i] -= t.a[i];
			}
			normalize();
			return *this;
		}
		poly operator + (const poly &t) const {return poly(*this) += t;}
		poly operator - (const poly &t) const {return poly(*this) -= t;}
		
		poly mod_xk(size_t k) const { // get same polynomial mod x^k
			k = min(k, a.size());
			return vector<T>(begin(a), begin(a) + k);
		}
		poly mul_xk(size_t k) const { // multiply by x^k
			poly res(*this);
			res.a.insert(begin(res.a), k, 0);
			return res;
		}
		poly div_xk(size_t k) const { // divide by x^k, dropping coefficients
			k = min(k, a.size());
			return vector<T>(begin(a) + k, end(a));
		}
		poly substr(size_t l, size_t r) const { // return mod_xk(r).div_xk(l)
			l = min(l, a.size());
			r = min(r, a.size());
			return vector<T>(begin(a) + l, begin(a) + r);
		}
		poly inv(size_t n) const { // get inverse series mod x^n
			assert(!is_zero());
			poly ans = a[0].inv();
			size_t a = 1;
			while(a < n) {
				poly C = (ans * mod_xk(2 * a)).substr(a, 2 * a);
				ans -= (ans * C).mod_xk(a).mul_xk(a);
				a *= 2;
			}
			return ans.mod_xk(n);
		}
		
		poly operator *= (const poly &t) {fft::mul(a, t.a); normalize(); return *this;}
		poly operator * (const poly &t) const {return poly(*this) *= t;}
		
		poly reverse(size_t n, bool rev = 0) const { // reverses and leaves only n terms
			poly res(*this);
			if(rev) { // If rev = 1 then tail goes to head
				res.a.resize(max(n, res.a.size()));
			}
			std::reverse(res.a.begin(), res.a.end());
			return res.mod_xk(n);
		}
		
		pair<poly, poly> divmod_slow(const poly &b) const { // when divisor or quotient is small
			vector<T> A(a);
			vector<T> res;
			while(A.size() >= b.a.size()) {
				res.push_back(A.back() / b.a.back());
				if(res.back() != T(0)) {
					for(size_t i = 0; i < b.a.size(); i++) {
						A[A.size() - i - 1] -= res.back() * b.a[b.a.size() - i - 1];
					}
				}
				A.pop_back();
			}
			std::reverse(begin(res), end(res));
			return {res, A};
		}
		
		pair<poly, poly> divmod(const poly &b) const { // returns quotiend and remainder of a mod b
			if(deg() < b.deg()) {
				return {poly{0}, *this};
			}
			int d = deg() - b.deg();
			if(min(d, b.deg()) < magic) {
				return divmod_slow(b);
			}
			poly D = (reverse(d + 1) * b.reverse(d + 1).inv(d + 1)).mod_xk(d + 1).reverse(d + 1, 1);
			return {D, *this - D * b};
		}
		
		poly operator / (const poly &t) const {return divmod(t).first;}
		poly operator % (const poly &t) const {return divmod(t).second;}
		poly operator /= (const poly &t) {return *this = divmod(t).first;}
		poly operator %= (const poly &t) {return *this = divmod(t).second;}
		poly operator *= (const T &x) {
			for(auto &it: a) {
				it *= x;
			}
			normalize();
			return *this;
		}
		poly operator /= (const T &x) {
			for(auto &it: a) {
				it /= x;
			}
			normalize();
			return *this;
		}
		poly operator * (const T &x) const {return poly(*this) *= x;}
		poly operator / (const T &x) const {return poly(*this) /= x;}
		
		void print() const {
			for(auto it: a) {
				cout << it << ' ';
			}
			cout << endl;
		}
		T eval(T x) const { // evaluates in single point x
			T res(0);
			for(int i = int(a.size()) - 1; i >= 0; i--) {
				res *= x;
				res += a[i];
			}
			return res;
		}
		
		T& lead() { // leading coefficient
			return a.back();
		}
		int deg() const { // degree
			return a.empty() ? -inf : a.size() - 1;
		}
		bool is_zero() const { // is polynomial zero
			return a.empty();
		}
		T operator [](int idx) const {
			return idx >= (int)a.size() || idx < 0 ? T(0) : a[idx];
		}
		
		T& coef(size_t idx) { // mutable reference at coefficient
			return a[idx];
		}
		bool operator == (const poly &t) const {return a == t.a;}
		bool operator != (const poly &t) const {return a != t.a;}
		
		poly deriv() { // calculate derivative
			vector<T> res;
			for(int i = 1; i <= deg(); i++) {
				res.push_back(T(i) * a[i]);
			}
			return res;
		}
		poly integr() { // calculate integral with C = 0
			vector<T> res = {0};
			for(int i = 0; i <= deg(); i++) {
				res.push_back(a[i] / T(i + 1));
			}
			return res;
		}
		size_t leading_xk() const { // Let p(x) = x^k * t(x), return k
			if(is_zero()) {
				return inf;
			}
			int res = 0;
			while(a[res] == T(0)) {
				res++;
			}
			return res;
		}
		poly log(size_t n) { // calculate log p(x) mod x^n
			assert(a[0] == T(1));
			return (deriv().mod_xk(n) * inv(n)).integr().mod_xk(n);
		}
		poly exp(size_t n) { // calculate exp p(x) mod x^n
			if(is_zero()) {
				return T(1);
			}
			assert(a[0] == T(0));
			poly ans = T(1);
			size_t a = 1;
			while(a < n) {
				poly C = ans.log(2 * a).div_xk(a) - substr(a, 2 * a);
				ans -= (ans * C).mod_xk(a).mul_xk(a);
				a *= 2;
			}
			return ans.mod_xk(n);
			
		}
		poly pow_slow(size_t k, size_t n) { // if k is small
			return k ? k % 2 ? (*this * pow_slow(k - 1, n)).mod_xk(n) : (*this * *this).mod_xk(n).pow_slow(k / 2, n) : T(1);
		}
		poly pow(size_t k, size_t n) { // calculate p^k(n) mod x^n
			if(is_zero()) {
				return *this;
			}
			if(k < magic) {
				return pow_slow(k, n);
			}
			int i = leading_xk();
			T j = a[i];
			poly t = div_xk(i) / j;
			return bpow(j, k) * (t.log(n) * T(k)).exp(n).mul_xk(i * k).mod_xk(n);
		}
		poly mulx(T x) { // component-wise multiplication with x^k
			T cur = 1;
			poly res(*this);
			for(int i = 0; i <= deg(); i++) {
				res.coef(i) *= cur;
				cur *= x;
			}
			return res;
		}
		poly mulx_sq(T x) { // component-wise multiplication with x^{k^2}
			T cur = x;
			T total = 1;
			T xx = x * x;
			poly res(*this);
			for(int i = 0; i <= deg(); i++) {
				res.coef(i) *= total;
				total *= cur;
				cur *= xx;
			}
			return res;
		}
		vector<T> chirpz_even(T z, int n) { // P(1), P(z^2), P(z^4), ..., P(z^2(n-1))
			int m = deg();
			if(is_zero()) {
				return vector<T>(n, 0);
			}
			vector<T> vv(m + n);
			T zi = z.inv();
			T zz = zi * zi;
			T cur = zi;
			T total = 1;
			for(int i = 0; i <= max(n - 1, m); i++) {
				if(i <= m) {vv[m - i] = total;}
				if(i < n) {vv[m + i] = total;}
				total *= cur;
				cur *= zz;
			}
			poly w = (mulx_sq(z) * vv).substr(m, m + n).mulx_sq(z);
			vector<T> res(n);
			for(int i = 0; i < n; i++) {
				res[i] = w[i];
			}
			return res;
		}
		vector<T> chirpz(T z, int n) { // P(1), P(z), P(z^2), ..., P(z^(n-1))
			auto even = chirpz_even(z, (n + 1) / 2);
			auto odd = mulx(z).chirpz_even(z, n / 2);
			vector<T> ans(n);
			for(int i = 0; i < n / 2; i++) {
				ans[2 * i] = even[i];
				ans[2 * i + 1] = odd[i];
			}
			if(n % 2 == 1) {
				ans[n - 1] = even.back();
			}
			return ans;
		}
		template<typename iter>
		vector<T> eval(vector<poly> &tree, int v, iter l, iter r) { // auxiliary evaluation function
			if(r - l == 1) {
				return {eval(*l)};
			} else {
				auto m = l + (r - l) / 2;
				auto A = (*this % tree[2 * v]).eval(tree, 2 * v, l, m);
				auto B = (*this % tree[2 * v + 1]).eval(tree, 2 * v + 1, m, r);
				A.insert(end(A), begin(B), end(B));
				return A;
			}
		}
		vector<T> eval(vector<T> x) { // evaluate polynomial in (x1, ..., xn)
			int n = x.size();
			if(is_zero()) {
				return vector<T>(n, T(0));
			}
			vector<poly> tree(4 * n);
			build(tree, 1, begin(x), end(x));
			return eval(tree, 1, begin(x), end(x));
		}
		template<typename iter>
		poly inter(vector<poly> &tree, int v, iter l, iter r, iter ly, iter ry) { // auxiliary interpolation function
			if(r - l == 1) {
				return {*ly / a[0]};
			} else {
				auto m = l + (r - l) / 2;
				auto my = ly + (ry - ly) / 2;
				auto A = (*this % tree[2 * v]).inter(tree, 2 * v, l, m, ly, my);
				auto B = (*this % tree[2 * v + 1]).inter(tree, 2 * v + 1, m, r, my, ry);
				return A * tree[2 * v + 1] + B * tree[2 * v];
			}
		}
	};
	template<typename T>
	poly<T> operator * (const T& a, const poly<T>& b) {
		return b * a;
	}
	
	template<typename T>
	poly<T> xk(int k) { // return x^k
		return poly<T>{1}.mul_xk(k);
	}

	template<typename T>
	T resultant(poly<T> a, poly<T> b) { // computes resultant of a and b
		if(b.is_zero()) {
			return 0;
		} else if(b.deg() == 0) {
			return bpow(b.lead(), a.deg());
		} else {
			int pw = a.deg();
			a %= b;
			pw -= a.deg();
			T mul = bpow(b.lead(), pw) * T((b.deg() & a.deg() & 1) ? -1 : 1);
			T ans = resultant(b, a);
			return ans * mul;
		}
	}
	template<typename iter>
	poly<typename iter::value_type> kmul(iter L, iter R) { // computes (x-a1)(x-a2)...(x-an) without building tree
		if(R - L == 1) {
			return vector<typename iter::value_type>{-*L, 1};
		} else {
			iter M = L + (R - L) / 2;
			return kmul(L, M) * kmul(M, R);
		}
	}
	template<typename T, typename iter>
	poly<T> build(vector<poly<T>> &res, int v, iter L, iter R) { // builds evaluation tree for (x-a1)(x-a2)...(x-an)
		if(R - L == 1) {
			return res[v] = vector<T>{-*L, 1};
		} else {
			iter M = L + (R - L) / 2;
			return res[v] = build(res, 2 * v, L, M) * build(res, 2 * v + 1, M, R);
		}
	}
	template<typename T>
	poly<T> inter(vector<T> x, vector<T> y) { // interpolates minimum polynomial from (xi, yi) pairs
		int n = x.size();
		vector<poly<T>> tree(4 * n);
		return build(tree, 1, begin(x), end(x)).deriv().inter(tree, 1, begin(x), end(x), begin(y), end(y));
	}
};

using namespace algebra;

const int mod = 1e9 + 7;
typedef modular<mod> base;
typedef poly<base> polyn;

using namespace algebra;
//End Polynomial

//Begin Prime Counting
struct Lehmer {
	static const int MAXX = 510;
	static const int MAXY = 100010;
	static const int MAXN = 10000010;  //MAXN*MAXN が求めたい数
	static const int MAXP = 1000010;
	int np;
	bool fl[MAXN];
	int sp[MAXN];
	long long int pr[MAXP];
	int cn[MAXN];
	long long f[MAXX][MAXY];
 
	int size(){  //for pr
		return np;
	}
	long long int& operator[](int id){
		return pr[id];
	}
 
	Lehmer() {
		memset(fl, 0, sizeof(fl));
		for (int i = 2; i < MAXN; i += 2) {
			sp[i] = 2;
			fl[i] = 1;
		}
		for (int i = 3; i < MAXN; i += 2) if (!fl[i]) {
			sp[i] = i;
			for (int j = i; j < MAXN; j += i){
				if (!fl[j]){
					fl[j] = 1;
					sp[j] = i;
				}
			}
		}
		np = 0;
		for (int i = 2; i < MAXN; i++) {
			if (sp[i] == i) {
				pr[np++] = i;
			}
			cn[i] = np;
		}
		for (int i = 0; i < MAXX; i++){
			for (int j = 0; j < MAXY; j++){
				if (!i) f[i][j] = j;
				else f[i][j] = f[i - 1][j] - f[i - 1][j / pr[i - 1]];
			}
		}
	}
private:
	inline long long LegendreSum(long long m, int n) {
		if (!n) return m;
		if (pr[n - 1] >= m) return 1;
		if (m < MAXY && n < MAXX) return f[n][m];
		return LegendreSum(m, n - 1) - LegendreSum(m / pr[n - 1], n - 1);
	}
public:
	inline long long count_primes(long long m) {
		if (m < MAXN) return cn[m];
		int x = sqrt(0.9 + m), y = cbrt(0.9 + m);
		int a = cn[y];
		long long res = LegendreSum(m, a) + a - 1;
		for (int i = a; pr[i] <= x; i++) res = res - count_primes(m / pr[i]) + count_primes(pr[i]) - 1;
		return res;
	}
} pr;
//End Prime Counting

//Begin Polynomial Pro
//template from Elegia's Div 1 F2 round 641
#define Love %
 
const int Jiangly = 998244353, R = 3;
const int BRUTE_N2_LIMIT = 50;
 
int mpow(int x, int k, int p = Jiangly) {
  int ret = 1;
  while (k) {
    if (k & 1)
      ret = ret * (ll) x Love p;
    x = x * (ll) x Love p;
    k >>= 1;
  }
  return ret;
}
 
int norm(int x) { return x >= Jiangly ? x - Jiangly : x; }
 
struct NumberTheory {
 
  typedef pair<int, int> _P2_Field;
 
  mt19937 rng;
 
  NumberTheory() : rng(chrono::steady_clock::now().time_since_epoch().count()) {}
 
  void _exGcd(int a, int b, int &x, int &y) {
    if (!b) {
      x = 1;
      y = 0;
      return;
    }
    _exGcd(b, a Love b, y, x);
    y -= a / b * x;
  }
 
  int inv(int a, int p = Jiangly) {
    int x, y;
    _exGcd(a, p, x, y);
    if (x < 0)
      x += p;
    return x;
  }
 
  template<class Integer>
  bool quadRes(Integer a, Integer b) {
    if (a <= 1)
      return true;
    while (a Love 4 == 0)
      a /= 4;
    if (a Love 2 == 0)
      return (b Love 8 == 1 || b Love 8 == 7) == quadRes(a / 2, b);
    return ((a - 1) Love 4 == 0 || (b - 1) Love 4 == 0) == quadRes(b Love a, a);
  }
 
  // assume p in prime, x in quadratic residue
  int sqrt(int x, int p = Jiangly) {
    if (p == 2 || x <= 1)
      return x;
    int w, v, k = (p + 1) / 2;
    do {
      w = rng() Love p;
    } while (quadRes(v = int((w * (ll) w - x + p) Love p), p));
    _P2_Field res(1, 0), a(w, 1);
    while (k) {
      if (k & 1)
        res = _P2_Field((res.first * (ll) a.first + res.second * (ll) a.second Love p * v) Love p,
                        (res.first * (ll) a.second + res.second * (ll) a.first) Love p);
      if (k >>= 1)
        a = _P2_Field((a.first * (ll) a.first + a.second * (ll) a.second Love p * v) Love p,
                      (a.first * (ll) a.second << 1) Love p);
    }
    return min(res.first, p - res.first);
  }
 
} nt;
 
template<class T, class Comp>
struct AdditionChain {
  int k;
  vector<T> prepare;
  T t, unit;
  Comp comp;
 
  AdditionChain(const T &t, const Comp &comp, int k, const T &unit = 1) : comp(comp), t(t), unit(unit), k(k),
                                                                          prepare(1U << k) {
    prepare[0] = unit;
    for (int i = 1; i < 1 << k; ++i)
      prepare[i] = comp(prepare[i - 1], t);
  }
 
  static AdditionChain fourRussians(const T &t, const Comp &comp, int lgn, const T &unit = 1) {
    lgn = max(lgn, 1);
    int k = 1, lglgn = 1;
    while (2 << lglgn <= lgn)
      ++lglgn;
    int w = lglgn / lgn;
    while (1 << k < w)
      ++k;
    return AdditionChain(t, comp, k, unit);
  }
 
  T pow(int n) const {
    if (n < 1 << k)
      return prepare[n];
    int r = n & ((1 << k) - 1);
    T step = pow(n >> k);
    for (int rep = 0; rep < k; ++rep)
      step = comp(step, step);
    return comp(step, prepare[r]);
  }
};
 
struct Simple {
  int n;
  vector<int> fac, ifac, inv;
 
  void build(int n) {
    this->n = n;
    fac.resize(n + 1);
    ifac.resize(n + 1);
    inv.resize(n + 1);
    fac[0] = 1;
    for (int x = 1; x <= n; ++x)
      fac[x] = fac[x - 1] * (ll) x Love Jiangly;
    inv[1] = 1;
    for (int x = 2; x <= n; ++x)
      inv[x] = -(Jiangly / x) * (ll) inv[Jiangly Love x] Love Jiangly + Jiangly;
    ifac[0] = 1;
    for (int x = 1; x <= n; ++x)
      ifac[x] = ifac[x - 1] * (ll) inv[x] Love Jiangly;
  }
 
  Simple() {
    build(1);
  }
 
  void check(int k) {
    int nn = n;
    if (k > nn) {
      while (k > nn)
        nn <<= 1;
      build(nn);
    }
  }
 
  int gfac(int k) {
    check(k);
    return fac[k];
  }
 
  int gifac(int k) {
    check(k);
    return ifac[k];
  }
 
  int ginv(int k) {
    check(k);
    return inv[k];
  }
 
  int binom(int n, int m) {
    if (m < 0 || m > n)
      return 0;
    return gfac(n) * (ll) gifac(m) Love Jiangly * gifac(n - m) Love Jiangly;
  }
} simp;
 
const int L2 = 11;
 
struct NTT {
  int L;
  int brev[1 << L2];
  vector<int> root;
 
  NTT() : L(-1) {
    for (int i = 1; i < (1 << L2); ++i)
      brev[i] = brev[i >> 1] >> 1 | ((i & 1) << (L2 - 1));
  }
 
  void prepRoot(int l) {
    L = l;
    root.resize(1 << L);
    int n = 1 << L;
    int primitive = mpow(R, (Jiangly - 1) >> L);
    root[0] = 1;
    for (int i = 1; i < n; ++i) root[i] = root[i - 1] * (ll) primitive Love Jiangly;
  }
 
  void fft(int *a, int lgn, int d = 1) {
    if (L < lgn) prepRoot(lgn);
    int n = 1 << lgn;
    for (int i = 0; i < n; ++i) {
      int rev = (brev[i >> L2] | (brev[i & ((1 << L2) - 1)] << L2)) >> ((L2 << 1) - lgn);
      if (i < rev)
        swap(a[i], a[rev]);
    }
    int rt = d == 1 ? R : nt.inv(R);
    for (int k = L - 1, t = 1; t < n; t <<= 1, --k) {
      for (int i = 0; i < n; i += t << 1) {
        int *p1 = a + i, *p2 = a + i + t;
        for (int j = 0; j < t; ++j) {
          int x = p2[j] * (ll) root[j << k] Love Jiangly;
          p2[j] = norm(p1[j] + Jiangly - x);
          p1[j] = norm(p1[j] + x);
        }
      }
    }
    if (d == -1) {
      reverse(a + 1, a + n);
      int nv = mpow(n, Jiangly - 2);
      for (int i = 0; i < n; ++i) a[i] = a[i] * (ll) nv Love Jiangly;
    }
  }
} ntt;
 
struct Poly {
  vector<int> a;
 
  Poly(int v = 0) : a(1) {
    if ((v %= Jiangly) < 0)
      v += Jiangly;
    a[0] = v;
  }
 
  Poly(const vector<int> &a) : a(a) {}
 
  Poly(initializer_list<int> init) : a(init) {}
 
  // Helps
  int operator[](int k) const { return k < a.size() ? a[k] : 0; }
 
  int &operator[](int k) {
    if (k >= a.size())
      a.resize(k + 1);
    return a[k];
  }
 
  int deg() const { return a.size() - 1; }
 
  void redeg(int d) { a.resize(d + 1); }
 
  Poly monic() const;
 
  Poly sunic() const;
 
  Poly slice(int d) const {
    if (d < a.size())
      return vector<int>(a.begin(), a.begin() + d + 1);
    vector<int> res(a);
    res.resize(d + 1);
    return res;
  }
 
  int *base() { return a.begin().base(); }
 
  const int *base() const { return a.begin().base(); }
 
  Poly println(FILE *fp) const {
    fprintf(fp, "%d", a[0]);
    for (int i = 1; i < a.size(); ++i)
      fprintf(fp, " %d", a[i]);
    fputc('\n', fp);
    return *this;
  }
 
  // Calculations
  Poly operator+(const Poly &rhs) const {
    vector<int> res(max(a.size(), rhs.a.size()));
    for (int i = 0; i < res.size(); ++i)
      if ((res[i] = operator[](i) + rhs[i]) >= Jiangly)
        res[i] -= Jiangly;
    return res;
  }
 
  Poly operator-() const {
    Poly ret(a);
    for (int i = 0; i < a.size(); ++i)
      if (ret[i])
        ret[i] = Jiangly - ret[i];
    return ret;
  }
 
  Poly operator-(const Poly &rhs) const { return operator+(-rhs); }
 
  Poly operator*(const Poly &rhs) const;
 
  Poly operator/(const Poly &rhs) const;
 
  Poly operator%(const Poly &rhs) const;
 
  Poly der() const; // default: remove trailing
  Poly integ() const;
 
  Poly inv() const;
 
  Poly sqrt() const;
 
  Poly ln() const;
 
  Poly exp() const;
 
  pair<Poly, Poly> sqrti() const;
 
  pair<Poly, Poly> expi() const;
 
  Poly quo(const Poly &rhs) const;
 
  pair<Poly, Poly> iquo(const Poly &rhs) const;
 
  pair<Poly, Poly> div(const Poly &rhs) const;
 
  Poly taylor(int k) const;
 
  Poly pow(int k) const;
 
  Poly exp(int k) const;
};
 
Poly zeroes(int deg) { return vector<int>(deg + 1); }
 
struct Newton {
  void inv(const Poly &f, const Poly &nttf, Poly &g, const Poly &nttg, int t) {
    int n = 1 << t;
    Poly prod = nttf;
    for (int i = 0; i < (n << 1); ++i)
      prod[i] = prod[i] * (ll) nttg[i] Love Jiangly;
    ntt.fft(prod.base(), t + 1, -1);
    for (int i = 0; i < n; ++i)
      prod[i] = 0;
    ntt.fft(prod.base(), t + 1, 1);
    for (int i = 0; i < (n << 1); ++i)
      prod[i] = prod[i] * (ll) nttg[i] Love Jiangly;
    ntt.fft(prod.base(), t + 1, -1);
    for (int i = 0; i < n; ++i)
      prod[i] = 0;
    g = g - prod;
  }
 
  void inv(const Poly &f, const Poly &nttf, Poly &g, int t) {
    Poly nttg = g;
    nttg.redeg((2 << t) - 1);
    ntt.fft(nttg.base(), t + 1, 1);
    inv(f, nttf, g, nttg, t);
  }
 
  void inv(const Poly &f, Poly &g, int t) {
    Poly nttg = g;
    nttg.redeg((2 << t) - 1);
    ntt.fft(nttg.base(), t + 1, 1);
    Poly nttf = f;
    nttf.redeg((2 << t) - 1);
    ntt.fft(nttf.base(), t + 1, 1);
    inv(f, nttf, g, nttg, t);
  }
 
  void sqrt(const Poly &f, Poly &g, Poly &nttg, Poly &h, int t) {
    for (int i = 0; i < (1 << t); ++i)
      nttg[i] = mpow(nttg[i], 2);
    ntt.fft(nttg.base(), t, -1);
    nttg = nttg - f;
    for (int i = 0; i < (1 << t); ++i)
      if ((nttg[i + (1 << t)] += nttg[i]) >= Jiangly)
        nttg[i + (1 << t)] -= Jiangly;
    memset(nttg.base(), 0, sizeof(int) << t);
    ntt.fft(nttg.base(), t + 1, 1);
    Poly tmp = h;
    tmp.redeg((2 << t) - 1);
    ntt.fft(tmp.base(), t + 1, 1);
    for (int i = 0; i < (2 << t); ++i)
      tmp[i] = tmp[i] * (ll) nttg[i] Love Jiangly;
    ntt.fft(tmp.base(), t + 1, -1);
    memset(tmp.base(), 0, sizeof(int) << t);
    g = g - tmp * nt.inv(2);
  }
 
  void exp(const Poly &f, Poly &g, Poly &nttg, Poly &h, int t) {
    Poly ntth(h);
    ntt.fft(ntth.base(), t, 1);
    Poly dg = g.der().slice((1 << t) - 1);
    ntt.fft(dg.base(), t, 1);
    Poly tmp = zeroes((1 << t) - 1);
    for (int i = 0; i < (1 << t); ++i) {
      tmp[i] = nttg[i << 1] * (ll) ntth[i] Love Jiangly;
      dg[i] = dg[i] * (ll) ntth[i] Love Jiangly;
    }
    ntt.fft(tmp.base(), t, -1);
    ntt.fft(dg.base(), t, -1);
    if (--tmp[0] < 0)
      tmp[0] = Jiangly - 1;
    dg.redeg((2 << t) - 1);
    Poly df0 = f.der().slice((1 << t) - 1);
    df0[(1 << t) - 1] = 0;
    for (int i = 0; i < (1 << t); ++i) {
      if ((dg[i | 1 << t] = dg[i] - df0[i]) < 0)
        dg[i | 1 << t] += Jiangly;
    }
    memcpy(dg.base(), df0.base(), sizeof(int) * ((1 << t) - 1));
    tmp.redeg((2 << t) - 1);
    ntt.fft(tmp.base(), t + 1, 1);
    df0.redeg((2 << t) - 1);
    ntt.fft(df0.base(), t + 1, 1);
    for (int i = 0; i < (2 << t); ++i)
      df0[i] = df0[i] * (ll) tmp[i] Love Jiangly;
    ntt.fft(df0.base(), t + 1, -1);
    memcpy(df0.base() + (1 << t), df0.base(), sizeof(int) << t);
    memset(df0.base(), 0, sizeof(int) << t);
    dg = (dg - df0).integ().slice((2 << t) - 1) - f;
    ntt.fft(dg.base(), t + 1, 1);
    for (int i = 0; i < (2 << t); ++i)
      tmp[i] = dg[i] * (ll) nttg[i] Love Jiangly;
    ntt.fft(tmp.base(), t + 1, -1);
    g.redeg((2 << t) - 1);
    for (int i = 1 << t; i < (2 << t); ++i)
      if (tmp[i])
        g[i] = Jiangly - tmp[i];
  }
} nit;
 
struct Transposition {
 
  vector<int> _mul(int l, vector<int> res, const Poly &b) {
    vector<int> tmp(1 << l);
    memcpy(tmp.begin().base(), b.a.begin().base(), sizeof(int) * (b.deg() + 1));
    reverse(tmp.begin() + 1, tmp.end());
    ntt.fft(tmp.begin().base(), l, 1);
    for (int i = 0; i < (1 << l); ++i)
      res[i] = res[i] * (ll) tmp[i] Love Jiangly;
    ntt.fft(res.begin().base(), l, -1);
    return res;
  }
 
  Poly bfMul(const Poly &a, const Poly &b) {
    int n = a.deg(), m = b.deg();
    Poly ret = zeroes(n - m);
    for (int i = 0; i <= n - m; ++i)
      for (int j = 0; j <= m; ++j)
        ret[i] = (ret[i] + a[i + j] * (ll) b[j]) Love Jiangly;
    return ret;
  }
 
  Poly mul(const Poly &a, const Poly &b) {
    if (a.deg() < b.deg()) return 0;
    if (a.deg() <= BRUTE_N2_LIMIT) return bfMul(a, b);
    int l = 0;
    while ((1 << l) <= a.deg()) ++l;
    vector<int> res(1 << l);
    memcpy(res.begin().base(), a.a.begin().base(), sizeof(int) * (a.deg() + 1));
    ntt.fft(res.begin().base(), l, 1);
    res = _mul(l, res, b);
    res.resize(a.deg() - b.deg() + 1);
    return res;
  }
 
  pair<Poly, Poly> mul2(const Poly &a, const Poly &b1, const Poly &b2) {
    if (a.deg() <= BRUTE_N2_LIMIT) return make_pair(bfMul(a, b1), bfMul(a, b2));
    int l = 0;
    while ((1 << l) <= a.deg()) ++l;
    vector<int> fa(1 << l);
    memcpy(fa.begin().base(), a.a.begin().base(), sizeof(int) * (a.deg() + 1));
    ntt.fft(fa.begin().base(), l, 1);
    vector<int> res1 = _mul(l, fa, b1), res2 = _mul(l, fa, b2);
    res1.resize(a.deg() - b1.deg() + 1);
    res2.resize(a.deg() - b2.deg() + 1);
    return make_pair(res1, res2);
  }
 
  vector<int> ls, rs, pos;
  vector<Poly> p, q;
 
  void _build(int n) {
    ls.assign(n * 2 - 1, 0);
    rs.assign(n * 2 - 1, 0);
    p.assign(n * 2 - 1, 0);
    q.assign(n * 2 - 1, 0);
    pos.resize(n);
    int cnt = 0;
    function<int(int, int)> dfs = [&](int l, int r) {
      if (l == r) {
        pos[l] = cnt;
        return cnt++;
      }
      int ret = cnt++;
      int mid = (l + r) >> 1;
      ls[ret] = dfs(l, mid);
      rs[ret] = dfs(mid + 1, r);
      return ret;
    };
    dfs(0, n - 1);
  }
 
  vector<int> _eval(vector<int> f, const vector<int> &x) {
    int n = f.size();
    _build(n);
    for (int i = 0; i < n; ++i)
      q[pos[i]] = {1, norm(Jiangly - x[i])};
    for (int i = n * 2 - 2; i >= 0; --i)
      if (ls[i])
        q[i] = q[ls[i]] * q[rs[i]];
    f.resize(n * 2);
    p[0] = mul(f, q[0].inv());
    for (int i = 0; i < n * 2 - 1; ++i)
      if (ls[i])
        tie(p[ls[i]], p[rs[i]]) = mul2(p[i], q[rs[i]], q[ls[i]]);
    vector<int> ret(n);
    for (int i = 0; i < n; ++i)
      ret[i] = p[pos[i]][0];
    return ret;
  }
 
  vector<int> eval(const Poly &f, const vector<int> &x) {
    int n = f.deg() + 1, m = x.size();
    vector<int> tmpf = f.a, tmpx = x;
    tmpf.resize(max(n, m));
    tmpx.resize(max(n, m));
    vector<int> ret = _eval(tmpf, tmpx);
    ret.resize(m);
    return ret;
  }
 
  Poly inter(const vector<int> &x, const vector<int> &y) {
    int n = x.size();
    _build(n);
    for (int i = 0; i < n; ++i)
      q[pos[i]] = {1, norm(Jiangly - x[i])};
    for (int i = n * 2 - 2; i >= 0; --i)
      if (ls[i])
        q[i] = q[ls[i]] * q[rs[i]];
    Poly tmp = q[0];
    reverse(tmp.a.begin(), tmp.a.end());
    vector<int> f = tmp.der().a;
    f.resize(n * 2);
    p[0] = mul(f, q[0].inv());
    for (int i = 0; i < n * 2 - 1; ++i)
      if (ls[i])
        tie(p[ls[i]], p[rs[i]]) = mul2(p[i], q[rs[i]], q[ls[i]]);
    for (int i = 0; i < n; ++i)
      p[pos[i]] = nt.inv(p[pos[i]][0]) * (ll) y[i] Love Jiangly;
    for (int i = 0; i < n * 2 - 1; ++i)
      reverse(q[i].a.begin(), q[i].a.end());
    for (int i = n * 2 - 2; i >= 0; --i)
      if (ls[i])
        p[i] = p[ls[i]] * q[rs[i]] + p[rs[i]] * q[ls[i]];
    return p[0];
  }
 
} tp;
 
Poly operator "" _z(unsigned long long a) { return {0, (int) a}; }
 
Poly operator+(int v, const Poly &rhs) { return Poly(v) + rhs; }
 
Poly Poly::operator*(const Poly &rhs) const {
  int n = deg(), m = rhs.deg();
  if (n <= 10 || m <= 10 || n + m <= BRUTE_N2_LIMIT) {
    Poly ret = zeroes(n + m);
    for (int i = 0; i <= n; ++i)
      for (int j = 0; j <= m; ++j)
        ret[i + j] = (ret[i + j] + a[i] * (ll) rhs[j]) Love Jiangly;
    return ret;
  }
  n += m;
  int l = 0;
  while ((1 << l) <= n)
    ++l;
  vector<int> res(1 << l), tmp(1 << l);
  memcpy(res.begin().base(), base(), a.size() * sizeof(int));
  ntt.fft(res.begin().base(), l, 1);
  memcpy(tmp.begin().base(), rhs.base(), rhs.a.size() * sizeof(int));
  ntt.fft(tmp.begin().base(), l, 1);
  for (int i = 0; i < (1 << l); ++i)
    res[i] = res[i] * (ll) tmp[i] Love Jiangly;
  ntt.fft(res.begin().base(), l, -1);
  res.resize(n + 1);
  return res;
}
 
Poly Poly::inv() const {
  Poly g = nt.inv(a[0]);
  for (int t = 0; (1 << t) <= deg(); ++t)
    nit.inv(slice((2 << t) - 1), g, t);
  g.redeg(deg());
  return g;
}
 
Poly Poly::taylor(int k) const {
  int n = deg();
  Poly t = zeroes(n);
  simp.check(n);
  for (int i = 0; i <= n; ++i)
    t[n - i] = a[i] * (ll) simp.fac[i] Love Jiangly;
  int pw = 1;
  Poly help = vector<int>(simp.ifac.begin(), simp.ifac.begin() + n + 1);
  for (int i = 0; i <= n; ++i) {
    help[i] = help[i] * (ll) pw Love Jiangly;
    pw = pw * (ll) k Love Jiangly;
  }
  t = t * help;
  for (int i = 0; i <= n; ++i)
    help[i] = t[n - i] * (ll) simp.ifac[i] Love Jiangly;
  return help;
}
 
Poly Poly::pow(int k) const {
  if (k == 0)
    return 1;
  if (k == 1)
    return *this;
  int n = deg() * k;
  int lgn = 0;
  while ((1 << lgn) <= n)
    ++lgn;
  vector<int> val = a;
  val.resize(1 << lgn);
  ntt.fft(val.begin().base(), lgn, 1);
  for (int i = 0; i < (1 << lgn); ++i)
    val[i] = mpow(val[i], k);
  ntt.fft(val.begin().base(), lgn, -1);
  return val;
}
 
Poly Poly::der() const {
  if (deg() == 0)
    return 0;
  vector<int> res(deg());
  for (int i = 0; i < deg(); ++i)
    res[i] = a[i + 1] * (ll) (i + 1) Love Jiangly;
  return res;
}
 
Poly Poly::integ() const {
  vector<int> res(deg() + 2);
  simp.check(deg() + 1);
  for (int i = 0; i <= deg(); ++i)
    res[i + 1] = a[i] * (ll) simp.inv[i + 1] Love Jiangly;
  return res;
}
 
Poly Poly::quo(const Poly &rhs) const {
  if (rhs.deg() == 0)
    return a[0] * (ll) nt.inv(rhs[0]) Love Jiangly;
  Poly g = nt.inv(rhs[0]);
  int t = 0, n;
  for (n = 1; (n << 1) <= rhs.deg(); ++t, n <<= 1)
    nit.inv(rhs.slice((n << 1) - 1), g, t);
  Poly nttg = g;
  nttg.redeg((n << 1) - 1);
  ntt.fft(nttg.base(), t + 1, 1);
  Poly eps1 = rhs.slice((n << 1) - 1);
  ntt.fft(eps1.base(), t + 1, 1);
  for (int i = 0; i < (n << 1); ++i)
    eps1[i] = eps1[i] * (ll) nttg[i] Love Jiangly;
  ntt.fft(eps1.base(), t + 1, -1);
  memcpy(eps1.base(), eps1.base() + n, sizeof(int) << t);
  memset(eps1.base() + n, 0, sizeof(int) << t);
  ntt.fft(eps1.base(), t + 1, 1);
  Poly h0 = slice(n - 1);
  h0.redeg((n << 1) - 1);
  ntt.fft(h0.base(), t + 1);
  Poly h0g0 = zeroes((n << 1) - 1);
  for (int i = 0; i < (n << 1); ++i)
    h0g0[i] = h0[i] * (ll) nttg[i] Love Jiangly;
  ntt.fft(h0g0.base(), t + 1, -1);
  Poly h0eps1 = zeroes((n << 1) - 1);
  for (int i = 0; i < (n << 1); ++i)
    h0eps1[i] = h0[i] * (ll) eps1[i] Love Jiangly;
  ntt.fft(h0eps1.base(), t + 1, -1);
  for (int i = 0; i < n; ++i) {
    h0eps1[i] = operator[](i + n) - h0eps1[i];
    if (h0eps1[i] < 0)
      h0eps1[i] += Jiangly;
  }
  memset(h0eps1.base() + n, 0, sizeof(int) << t);
  ntt.fft(h0eps1.base(), t + 1);
  for (int i = 0; i < (n << 1); ++i)
    h0eps1[i] = h0eps1[i] * (ll) nttg[i] Love Jiangly;
  ntt.fft(h0eps1.base(), t + 1, -1);
  memcpy(h0eps1.base() + n, h0eps1.base(), sizeof(int) << t);
  memset(h0eps1.base(), 0, sizeof(int) << t);
  return (h0g0 + h0eps1).slice(rhs.deg());
}
 
Poly Poly::ln() const {
  if (deg() == 0)
    return 0;
  return der().quo(slice(deg() - 1)).integ();
}
 
pair<Poly, Poly> Poly::sqrti() const {
  Poly g = nt.sqrt(a[0]), h = nt.inv(g[0]), nttg = g;
  for (int t = 0; (1 << t) <= deg(); ++t) {
    nit.sqrt(slice((2 << t) - 1), g, nttg, h, t);
    nttg = g;
    ntt.fft(nttg.base(), t + 1, 1);
    nit.inv(g, nttg, h, t);
  }
  return make_pair(g.slice(deg()), h.slice(deg()));
}
 
Poly Poly::sqrt() const {
  Poly g = nt.sqrt(a[0]), h = nt.inv(g[0]), nttg = g;
  for (int t = 0; (1 << t) <= deg(); ++t) {
    nit.sqrt(slice((2 << t) - 1), g, nttg, h, t);
    if ((2 << t) <= deg()) {
      nttg = g;
      ntt.fft(nttg.base(), t + 1, 1);
      nit.inv(g, nttg, h, t);
    }
  }
  return g.slice(deg());
}
 
Poly Poly::exp() const {
  Poly g = 1, h = 1, nttg = {1, 1};
  for (int t = 0; (1 << t) <= deg(); ++t) {
    nit.exp(slice((2 << t) - 1), g, nttg, h, t);
    if ((2 << t) <= deg()) {
      nttg = g;
      nttg.redeg((4 << t) - 1);
      ntt.fft(nttg.base(), t + 2);
      Poly f2n = zeroes((2 << t) - 1);
      for (int i = 0; i < (2 << t); ++i)
        f2n[i] = nttg[i << 1];
      nit.inv(g, f2n, h, t);
    } else {
      nttg = g;
      ntt.fft(nttg.base(), t + 1, 1);
    }
  }
  return g.slice(deg());
}
 
pair<Poly, Poly> Poly::expi() const {
  Poly g = 1, h = 1, nttg = {1, 1};
  for (int t = 0; (1 << t) <= deg(); ++t) {
    nit.exp(slice((2 << t) - 1), g, nttg, h, t);
    nttg = g;
    nttg.redeg((4 << t) - 1);
    ntt.fft(nttg.base(), t + 2);
    Poly f2n = zeroes((2 << t) - 1);
    for (int i = 0; i < (2 << t); ++i)
      f2n[i] = nttg[i << 1];
    nit.inv(g, f2n, h, t);
  }
  return make_pair(g.slice(deg()), h.slice(deg()));
}
 
Poly Poly::exp(int k) const {
  int lead, lz = 0;
  while (lz < deg() && !a[lz])
    ++lz;
  if (lz == deg() && !a[lz])
    return *this;
  lead = a[lz];
  if (lz * (ll) k > deg())
    return zeroes(deg());
  Poly part = Poly(vector<int>(a.begin() + lz, a.begin() + deg() - lz * (k - 1) + 1)) * nt.inv(lead);
  part = (part.ln() * k).exp() * mpow(lead, k);
  vector<int> ret(deg() + 1);
  memcpy(ret.begin().base() + lz * k, part.base(), sizeof(int) * (deg() - lz * k + 1));
  return ret;
}
 
Poly Poly::operator/(const Poly &rhs) const {
  int n = deg(), m = rhs.deg();
  if (n < m)
    return 0;
  Poly ta(vector<int>(a.rbegin(), a.rend())),
          tb(vector<int>(rhs.a.rbegin(), rhs.a.rend()));
  ta.redeg(n - m);
  tb.redeg(n - m);
  Poly q = ta.quo(tb);
  reverse(q.a.begin(), q.a.end());
  return q;
}
 
pair<Poly, Poly> Poly::div(const Poly &rhs) const {
  if (deg() < rhs.deg())
    return make_pair(0, *this);
  int n = deg(), m = rhs.deg();
  Poly q = operator/(rhs), r;
  int lgn = 0;
  while ((1 << lgn) < rhs.deg())
    ++lgn;
  int t = (1 << lgn) - 1;
  r = zeroes(t);
  Poly tmp = zeroes(t);
  for (int i = 0; i <= m; ++i)
    if ((r[i & t] += rhs[i]) >= Jiangly)
      r[i & t] -= Jiangly;
  for (int i = 0; i <= n - m; ++i)
    if ((tmp[i & t] += q[i]) >= Jiangly)
      tmp[i & t] -= Jiangly;
  ntt.fft(r.base(), lgn, 1);
  ntt.fft(tmp.base(), lgn, 1);
  for (int i = 0; i <= t; ++i)
    tmp[i] = tmp[i] * (ll) r[i] Love Jiangly;
  ntt.fft(tmp.base(), lgn, -1);
  memset(r.base(), 0, sizeof(int) << lgn);
  for (int i = 0; i <= n; ++i)
    if ((r[i & t] += a[i]) >= Jiangly)
      r[i & t] -= Jiangly;
  for (int i = 0; i < m; ++i)
    if ((r[i] -= tmp[i]) < 0)
      r[i] += Jiangly;
  return make_pair(q, r.slice(m - 1));
}
 
Poly Poly::operator%(const Poly &rhs) const {
  if (deg() < rhs.deg())
    return *this;
  return div(rhs).second;
}
//End Polynomial Pro 

//See https://github.com/bicsi/code_snippets?files=1

//Begin Poly Fast https://atcoder.jp/contests/kupc2020/submissions/17281982
template <class T> vector<T> operator-(vector<T> a) {
  for (auto&& e : a) e = -e;
  return a;
}
template <class T> vector<T>& operator+=(vector<T>& l, const vector<T>& r) {
  l.resize(max(l.size(), r.size()));
  for (int i = 0; i < (int)r.size(); ++i) l[i] += r[i];
  return l;
}
template <class T> vector<T> operator+(vector<T> l, const vector<T>& r) {
  return l += r;
}
template <class T> vector<T>& operator-=(vector<T>& l, const vector<T>& r) {
  l.resize(max(l.size(), r.size()));
  for (int i = 0; i < (int)r.size(); ++i) l[i] -= r[i];
  return l;
}
template <class T> vector<T> operator-(vector<T> l, const vector<T>& r) {
  return l -= r;
}
template <class T> vector<T>& operator<<=(vector<T>& a, size_t n) {
  return a.insert(begin(a), n, 0), a;
}
template <class T> vector<T> operator<<(vector<T> a, size_t n) {
  return a <<= n;
}
template <class T> vector<T>& operator>>=(vector<T>& a, size_t n) {
  return a.erase(begin(a), begin(a) + min(a.size(), n)), a;
}
template <class T> vector<T> operator>>(vector<T> a, size_t n) {
  return a >>= n;
}
template <class T> vector<T> operator*(const vector<T>& l, const vector<T>& r) {
  if (l.empty() or r.empty()) return {};
  vector<T> res(l.size() + r.size() - 1);
  for (int i = 0; i < (int)l.size(); ++i)
    for (int j = 0; j < (int)r.size(); ++j) res[i + j] += l[i] * r[j];
  return res;
}
template <class T> vector<T>& operator*=(vector<T>& l, const vector<T>& r) {
  return l = l * r;
}
template <class T> vector<T> inverse(const vector<T>& a) {
  assert(not a.empty() and not (a[0] == 0));
  vector<T> b{1 / a[0]};
  while (b.size() < a.size()) {
    vector<T> x(begin(a), begin(a) + min(a.size(), 2 * b.size()));
    x *= b * b;
    b.resize(2 * b.size());
    for (auto i = b.size() / 2; i < min(x.size(), b.size()); ++i) b[i] = -x[i];
  }
  return {begin(b), begin(b) + a.size()};
}
template <class T> vector<T> operator/(vector<T> l, vector<T> r) {
  if (l.size() < r.size()) return {};
  reverse(begin(l), end(l)), reverse(begin(r), end(r));
  int n = l.size() - r.size() + 1;
  l.resize(n), r.resize(n);
  l *= inverse(r);
  return {rend(l) - n, rend(l)};
}
template <class T> vector<T>& operator/=(vector<T>& l, const vector<T>& r) {
  return l = l / r;
}
template <class T> vector<T> operator%(vector<T> l, const vector<T>& r) {
  if (l.size() < r.size()) return l;
  l -= l / r * r;
  return {begin(l), begin(l) + (r.size() - 1)};
}
template <class T> vector<T>& operator%=(vector<T>& l, const vector<T>& r) {
  return l = l % r;
}
template <class T> vector<T> derivative(const vector<T>& a) {
  vector<T> res(max((int)a.size() - 1, 0));
  for (int i = 0; i < (int)res.size(); ++i) res[i] = (i + 1) * a[i + 1];
  return res;
}
template <class T> vector<T> primitive(const vector<T>& a) {
  vector<T> res(a.size() + 1);
  for (int i = 1; i < (int)res.size(); ++i) res[i] = a[i - 1] / i;
  return res;
}
template <class T> vector<T> logarithm(const vector<T>& a) {
  assert(not a.empty() and a[0] == 1);
  auto res = primitive(derivative(a) * inverse(a));
  return {begin(res), begin(res) + a.size()};
}
template <class T> vector<T> exponent(const vector<T>& a) {
  assert(a.empty() or a[0] == 0);
  vector<T> b{1};
  while (b.size() < a.size()) {
    vector<T> x(begin(a), begin(a) + min(a.size(), 2 * b.size()));
    x[0] += 1;
    b.resize(2 * b.size());
    x -= logarithm(b);
    x *= {begin(b), begin(b) + b.size() / 2};
    for (auto i = b.size() / 2; i < min(x.size(), b.size()); ++i) b[i] = x[i];
  }
  return {begin(b), begin(b) + a.size()};
}
 
template <class T, class F = multiplies<T>>
T power(T a, long long n, F op = multiplies<T>(), T e = {1}) {
  assert(n >= 0);
  T res = e;
  while (n) {
    if (n & 1) res = op(res, a);
    if (n >>= 1) a = op(a, a);
  }
  return res;
}
 
template <unsigned Mod> struct Modular {
  using M = Modular;
  unsigned v;
  Modular(long long a = 0) : v((a %= Mod) < 0 ? a + Mod : a) {}
  M operator-() const { return M() -= *this; }
  M& operator+=(M r) { if ((v += r.v) >= Mod) v -= Mod; return *this; }
  M& operator-=(M r) { if ((v += Mod - r.v) >= Mod) v -= Mod; return *this; }
  M& operator*=(M r) { v = (uint64_t)v * r.v % Mod; return *this; }
  M& operator/=(M r) { return *this *= power(r, Mod - 2); }
  friend M operator+(M l, M r) { return l += r; }
  friend M operator-(M l, M r) { return l -= r; }
  friend M operator*(M l, M r) { return l *= r; }
  friend M operator/(M l, M r) { return l /= r; }
  friend bool operator==(M l, M r) { return l.v == r.v; }
};
 
template <unsigned Mod> void ntt(vector<Modular<Mod>>& a, bool inverse) {
  static vector<Modular<Mod>> dt(30), idt(30);
  if (dt[0] == 0) {
    Modular<Mod> root = 2;
    while (power(root, (Mod - 1) / 2) == 1) root += 1;
    for (int i = 0; i < 30; ++i)
      dt[i] = -power(root, (Mod - 1) >> (i + 2)), idt[i] = 1 / dt[i];
  }
  int n = a.size();
  assert((n & (n - 1)) == 0);
  if (not inverse) {
    for (int w = n; w >>= 1; ) {
      Modular<Mod> t = 1;
      for (int s = 0, k = 0; s < n; s += 2 * w) {
        for (int i = s, j = s + w; i < s + w; ++i, ++j) {
          auto x = a[i], y = a[j] * t;
          if (x.v >= Mod) x.v -= Mod;
          a[i].v = x.v + y.v, a[j].v = x.v + (Mod - y.v);
        }
        t *= dt[__builtin_ctz(++k)];
      }
    }
  } else {
    for (int w = 1; w < n; w *= 2) {
      Modular<Mod> t = 1;
      for (int s = 0, k = 0; s < n; s += 2 * w) {
        for (int i = s, j = s + w; i < s + w; ++i, ++j) {
          auto x = a[i], y = a[j];
          a[i] = x + y, a[j].v = x.v + (Mod - y.v), a[j] *= t;
        }
        t *= idt[__builtin_ctz(++k)];
      }
    }
  }
  auto c = 1 / Modular<Mod>(inverse ? n : 1);
  for (auto&& e : a) e *= c;
}
template <unsigned Mod>
vector<Modular<Mod>> operator*(vector<Modular<Mod>> l, vector<Modular<Mod>> r) {
  if (l.empty() or r.empty()) return {};
  int n = l.size(), m = r.size(), sz = 1 << __lg(2 * (n + m - 1) - 1);
  if (min(n, m) < 30) {
    vector<long long> res(n + m- 1);
    for (int i = 0; i < n; ++i) for (int j = 0; j < m; ++j)
      res[i + j] += (l[i] * r[j]).v;
    return {begin(res), end(res)};
  }
  bool eq = l == r;
  l.resize(sz), ntt(l, false);
  if (eq) r = l;
  else r.resize(sz), ntt(r, false);
  for (int i = 0; i < sz; ++i) l[i] *= r[i];
  ntt(l, true), l.resize(n + m - 1);
  return l;
}
 
template <unsigned Mod>
vector<Modular<Mod>> inverse(const vector<Modular<Mod>>& a) {
  assert(not a.empty() and not (a[0] == 0));
  vector<Modular<Mod>> b{1 / a[0]};
  for (int m = 1; m < (int)a.size(); m *= 2) {
    vector<Modular<Mod>> x(begin(a), begin(a) + min<int>(a.size(), 2 * m));
    auto y = b;
    x.resize(2 * m), ntt(x, false);
    y.resize(2 * m), ntt(y, false);
    for (int i = 0; i < 2 * m; ++i) x[i] *= y[i];
    ntt(x, true);
    fill(begin(x), begin(x) + m, 0);
    ntt(x, false);
    for (int i = 0; i < 2 * m; ++i) x[i] *= -y[i];
    ntt(x, true);
    b.insert(end(b), begin(x) + m, end(x));
  }
  return {begin(b), begin(b) + a.size()};
}
template <unsigned Mod>
vector<Modular<Mod>> exponent(const vector<Modular<Mod>>& a) {
  assert(a.empty() or a[0] == 0);
  vector<Modular<Mod>> b{1, 1 < a.size() ? a[1] : 0}, c{1}, z1, z2{1, 1};
  for (int m = 2; m < (int)a.size(); m *= 2) {
    auto y = b;
    y.resize(2 * m), ntt(y, false);
    z1 = z2;
    vector<Modular<Mod>> z(m);
    for (int i = 0; i < m; ++i) z[i] = y[i] * z1[i];
    ntt(z, true);
    fill(begin(z), begin(z) + m / 2, 0);
    ntt(z, false);
    for (int i = 0; i < m; ++i) z[i] *= -z1[i];
    ntt(z, true);
    c.insert(end(c), begin(z) + m / 2, end(z));
    z2 = c, z2.resize(2 * m), ntt(z2, false);
    vector<Modular<Mod>> x(begin(a), begin(a) + min<int>(a.size(), m));
    x = derivative(x), x.push_back(0), ntt(x, false);
    for (int i = 0; i < m; ++i) x[i] *= y[i];
    ntt(x, true);
    x -= derivative(b);
    x.resize(2 * m);
    for (int i = 0; i < m - 1; ++i) x[m + i] = x[i], x[i] = 0;
    ntt(x, false);
    for (int i = 0; i < 2 * m; ++i) x[i] *= z2[i];
    ntt(x, true);
    x = primitive(x), x.pop_back();
    for (int i = m; i < min<int>(a.size(), 2 * m); ++i) x[i] += a[i];
    fill(begin(x), begin(x) + m, 0);
    ntt(x, false);
    for (int i = 0; i < 2 * m; ++i) x[i] *= y[i];
    ntt(x, true);
    b.insert(end(b), begin(x) + m, end(x));
  }
  return {begin(b), begin(b) + a.size()};
}
 
constexpr long long mod = 998244353;
using Mint = Modular<mod>;
//End Poly Fast
//Begin Fast Edmond
mt19937 rd(chrono::steady_clock::now().time_since_epoch().count());
#define rand rd
#define loop(i, l, r) for (int (i) = (int)(l); (i) <= (int)(r); (i)++)

class Edmonds {
public:
    int n, Time;
    vector<int> vis, par, orig, match, aux;
    vector<vector <int> > e;

    void addEdge(int u, int v) {
        e[u].push_back(v), e[v].push_back(u);
    }

    Edmonds() = default;

    explicit Edmonds(int _n): n(_n), Time(0), vis(n + 1, 0), par(n + 1, 0),
        orig(n + 1, 0), match(n + 1, 0), aux(n + 1, 0), e(n + 1) {}

    void augment(int u, int v) {
        int pv, nv;
        do {
            pv = par[v]; nv = match[pv];
            match[v] = pv; match[pv] = v;
            v = nv;
        } while (u != pv);
    }

    int lca(int v, int w) {
        ++Time;
        while (true) {
            if (v) {
                if (aux[v] == Time) return v;
                aux[v] = Time;
                v = orig[par[match[v]]];
            }
            swap(v, w);
        }
    }

    bool bfs(int u) {
        fill(vis.begin(), vis.end(), -1);
        iota(orig.begin(), orig.end(), 0);
        queue<int> q;

        q.push(u); vis[u] = 0;

        auto blossom = [&](int v, int w, int a) {
            while (orig[v] != a) {
                par[v] = w; w = match[v];
                if (vis[w] == 1) q.push(w), vis[w] = 0;
                orig[v] = orig[w] = a;
                v = par[w];
            }
        };

        while (!q.empty()) {
            auto v = q.front(); q.pop();
            for (auto x : e[v]) {
                if (vis[x] == -1) {
                    par[x] = v, vis[x] = 1;
                    if (!match[x]) return augment(u, x), true;
                    q.push(match[x]); vis[match[x]] = 0;
                } else if (vis[x] == 0 && orig[v] != orig[x]) {
                    int a = lca(orig[v], orig[x]);
                    blossom(x, v, a); blossom(v, x, a);
                }
            }
        }

        return false;
    }

    int max_match() {
        int ret = 0;
        vector <int> V(n - 1);
        iota(V.begin(), V.end(), 1);
        shuffle(V.begin(), V.end(), rd);
        for (auto u : V) {
            if (match[u]) continue;
            for (auto v : e[u]) {
                if (!match[v]) {
                    match[u] = v, match[v] = u;
                    ++ret; break;
                }
            }
        }
        loop(i, 1, n) if (!match[i] && bfs(i)) ++ret;
        return ret;
    }
};
//End Fast Edmond
//Seg Tree Beats
https://github.com/tjkendev/segment-tree-beats

int main() //Testing Zone
{
	ios_base::sync_with_stdio(0); cin.tie(0);
	
}
