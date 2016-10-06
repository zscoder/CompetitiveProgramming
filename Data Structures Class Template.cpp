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
				st[i][j] = INF;
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
struct node2
{
	int p; ll sum;
};

struct DSU
{
	int S;
	vector<node2> dsu;
	
	DSU(int n)
	{
		S = n;
		for(int i = 0; i < n; i++)
		{
			node2 tmp;
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
template<int N> struct Matrix
{
	ll a[N][N];
	
	Matrix()
	{
		for (int i = 0; i < N; i++)
			for (int j = 0; j < N; j++)
				a[i][j] = (i == j ? 1 : 0);
	}

	Matrix operator * (const Matrix &A) const
	{
		Matrix R = Matrix();
		for (int i = 0; i < N; i++)
			for (int j = 0; j < N; j++)
			{
				R.a[i][j] = 0;
				for (int h = 0; h < N; h++)
				{
					R.a[i][j] += a[i][h] * A.a[h][j];
				}
			}
		return R;
	}
	
	Matrix binpow(Matrix A, ll p)
	{
		if(p == 0) return Matrix();
		if(p == 2 || (p&1)) return A*binpow(A, p - 1);
		return binpow(binpow(A, p/2), 2);
	}
};
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
struct suffix
{
	int index; // To store original index
	int rank[2]; // To store ranks and next rank pair
};

int cmp(suffix a, suffix b)
{
	return (a.rank[0] == b.rank[0])? (a.rank[1] < b.rank[1] ?1: 0):(a.rank[0] < b.rank[0] ?1: 0);
}

struct SuffixLCPArray //mostly/all from geeksforgeeks, to work for general alphabet remove the - 'a'
{	
	vector<suffix> suffixes;
	vi suffixArr;
	vi ind;
	void buildSA(const string& txt)
	{
		int n = txt.length();
		// A structure to store suffixes and their indexes
		
		suffixes.resize(n);
		// Store suffixes and their indexes in an array of structures.
		// The structure is needed to sort the suffixes alphabatically
		// and maintain their old indexes while sorting
		for (int i = 0; i < n; i++)
		{
			suffixes[i].index = i;
			suffixes[i].rank[0] = txt[i] - 'a';
			suffixes[i].rank[1] = ((i+1) < n)? (txt[i + 1] - 'a'): -1;
		}
	 
		// Sort the suffixes using the comparison function
		// defined above.
		sort(suffixes.begin(), suffixes.end(), cmp);
	 
		// At his point, all suffixes are sorted according to first
		// 2 characters.  Let us sort suffixes according to first 4
		// characters, then first 8 and so on
		ind.resize(n+1); // This array is needed to get the index in suffixes[]
					 // from original index.  This mapping is needed to get
					 // next suffix.
		for (int k = 4; k < 2*n; k = k*2)
		{
			// Assigning rank and index values to first suffix
			int rank = 0;
			int prev_rank = suffixes[0].rank[0];
			suffixes[0].rank[0] = rank;
			ind[suffixes[0].index] = 0;
	 
			// Assigning rank to suffixes
			for (int i = 1; i < n; i++)
			{
				// If first rank and next ranks are same as that of previous
				// suffix in array, assign the same new rank to this suffix
				if (suffixes[i].rank[0] == prev_rank && suffixes[i].rank[1] == suffixes[i-1].rank[1])
				{
					prev_rank = suffixes[i].rank[0];
					suffixes[i].rank[0] = rank;
				}
				else // Otherwise increment rank and assign
				{
					prev_rank = suffixes[i].rank[0];
					suffixes[i].rank[0] = ++rank;
				}
				ind[suffixes[i].index] = i;
			}
	 
			// Assign next rank to every suffix
			for (int i = 0; i < n; i++)
			{
				int nextindex = suffixes[i].index + k/2;
				suffixes[i].rank[1] = (nextindex < n)? suffixes[ind[nextindex]].rank[0]: -1;
			}
	 
			// Sort the suffixes according to first k characters
			sort(suffixes.begin(), suffixes.end(), cmp);
		}
	 
		// Store indexes of all sorted suffixes in the suffix array
		suffixArr.resize(n+1);
		for (int i = 0; i < n; i++)
		{
			suffixArr[i] = suffixes[i].index;
		}
	}
	
	vi rank;
	vi lcp;
	void buildLCP(string &s)
	{
		int n=s.size(),k=0;
		lcp.assign(n+1, 0);
		rank.assign(n,0);

		for(int i=0; i<n; i++) rank[suffixArr[i]]=i;

		for(int i=0; i<n; i++, k?k--:0)
		{
			if(rank[i]==n-1) {k=0; continue;}
			int j=suffixArr[rank[i]+1];
			while(i+k<n && j+k<n && s[i+k]==s[j+k]) k++;
			lcp[rank[i]]=k;
		}
	}
};
//End Suffix + LCP Array

/* TO-DO LIST :
1. SQRT DECOMP (MO)
2. SQRT DECOMP (REAL)
3. TREE (LCA, HLD)
8. SUFFIX ARRAY, LCP ARRAY
12. OTHER STRING STRUCTS SUCH AS PALINDROMIC TREE
14. FFT
15. Karatsuba
16. Other Flow Algo
17. KMP
18. Trie
19. Suffix Tree (?)
*/
int main() //Testing Zone
{
	ios_base::sync_with_stdio(0); cin.tie(0);
	
}
