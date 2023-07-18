#include <iostream>
#include <vector>
#include <cmath>
#include <ctime>
#include <cstdio>
#include <queue>
#include <set>
#include <map>
#include <fstream>
#include <cstdlib>
#include <string>
#include <cstring>
#include <algorithm>
#include <numeric>
#include <deque>
#include <iomanip> 
#include <iterator>
#include "ext/pb_ds/assoc_container.hpp"
#include "ext/pb_ds/tree_policy.hpp"
using namespace std;
using namespace __gnu_pbds;
using namespace std::chrono;


// ORDERED SET PBDS ( USE less<T> after null type for set and    less_equal<T> for multiset)
template<class T> 
using ordered_set = tree<T, null_type,less_equal<T>, rb_tree_tag, tree_order_statistics_node_update> ;
 
template<class key, class value, class cmp = std::less<key>>
using ordered_map = tree<key, value, cmp, rb_tree_tag, tree_order_statistics_node_update>;
// find_by_order(k)  returns iterator to kth element starting from 0;
// order_of_key(k) returns count of elements strictly smaller than k;

template<class T>
using min_heap = priority_queue<T,vector<T>,greater<T> >; 


//PRINT(VECTOR) AND  PRINT(VECTOR IN VECTOR)
template<typename T>
void printVector(const T& t) {
    std::copy(t.cbegin(), t.cend(), std::ostream_iterator<typename T::value_type>(std::cout, ", "));
    cout<<'\n';
}

template<typename T>
void printVectorInVector(const T& t){
    std::for_each(t.cbegin(), t.cend(), printVector<typename T::value_type>);
    cout<<'\n';
}




#define GODSPEED_SPIDERMAN ios:: sync_with_stdio(0);cin.tie(0);cout.tie(0);cout<<fixed;cout<<setprecision(15);
#define OH_oh(t) int t; cin>>t;
#define ll long long
#define pb(i) push_back(i);
#define all(a)  a.begin(), a.end()
#define gall(a) a.begin(), a.end(), greater<int>()
#define mp(a, b)  make_pair(a, b)
#define pbk  pop_back()
#define container_print(a) for(auto &it: a){ cout<<it<<" "; }
#define container_print_both(a) for(auto &it: a){ cout<<it.first<<" "<<it.second<<endl; }
#define check(i) cout<<i<<endl;
#define concatenate(a, b) a.insert(a.end(), b.begin(), b.end());




//CONSTANTS
const ll mod=1e9+7;
const ll moD=998244353;
const ll inf_big=1e18;
const ll inf=1e9;
const ll INF=1e18;
long double pi=2* acos(0.0);





// EUCLID GCD ALGORITHM
int gcd(int a, int b){
    if(b==0) return a;
    return gcd(b, a%b);
}
//EUCLID EXTENDED ALGORITHM
// if gcd(a, b)= k; then this egcd return to us such x, y that ax+by=k
pair<ll, ll> extended_gcd(ll a, ll b){
    if(b==0) return {1, 1};
    else{
        pair<ll, ll> z= extended_gcd(b, a%b);
        ll x= z.second, y= z.first- (a/b)*z.second;
        return {x, y};
    }
}





// MODULAR EXPONENTIATION WITHOUT MOD AND WITH MOD(FOR LARGE NUMBERS)
ll expo_mania(ll y, ll x){
    if(x==0) return 1;
    if(x==1) return y;
    else if(!(x&1)) return expo_mania(y*y, x/2);
    else return expo_mania(y*y, x/2)*y;
}
ll expo_mania(ll y, ll x, ll m){
    if(x==0) return 1;
    if(x==1) return y;
    else if(!(x&1)) return expo_mania((y*y)%m, (x/2)%m, m)%m;
    else return expo_mania((y*y)%m, (x/2)%m, m)*y%m;
}






//sieve of eratosthenes FIRST MARK ALL THE EVEN AND THEN MARK MULTIPLES LESS THAN 1e9 OF ALL REMANING ODD NUMBERS 
//WITHOUT MARKING THEMSELVES
int tarr[1];
void sieve(){
    tarr[1]=1;
    for(ll i=2; i*2<=9999998; i++){
        tarr[i*2]=1;
    }
    for(ll i=3; i<=9999; i+=2){
        for(ll j=2; j*i<=9999999; j++){
            tarr[j*i]=1;
        }
    }
}





//CONVERT DEGREES TO RADIANS BY MULTIPLYING IT WITH pie/180
double radian(double x){
    double ans=x*pi;
    ans=ans/(double)180;
    return ans;
}





//PRECALCULATION OF FACTORIALS TO DIRECTLY QUERY IN nCr AND nPr WRITTEN BELOW
int N=500050;
vector<ll> fac(N+9);
void prec(ll m){
    fac[0]=1;
    for(int i=1; i<N+1; i++){
        fac[i]=(fac[i-1]*i)%m;
    }
}
//nCr USING LITTLE FERMAT THEOREM
ll ncalr(ll x, ll y, ll m){
    if(x == y) return 1;
    if(y==0) return 1;
    ll n = fac[x];
    ll d = (fac[y]* fac[x-y]) %m;
    ll ans = (n * expo_mania(d, m-2, m) )%m;
    return ans;
}
ll npr(ll x, ll y, ll m){
    ll n= fac[x];
    ll d= fac[x-y];
    return (n/d)%m;
}   





// DISJOINT SET UNION OR UNION FIND TEMPLATE
struct disjoint_set{
    int n;
    vector<int> parent, size;
    // MAP FUNTIONALITY (#1)
    // map<int, set<int>> mp; //if you want to find which parent has how many children and in sorted order
    disjoint_set(int n){
        size.resize(n+1);
        fill(size.begin(), size.end(), 1);
        parent.resize(n+1);
        for(int i=1; i<=n; i++){
            parent[i]=i;
            // mp[1].insert(i);  //if you want to find which parent has how many children and in sorted order
        }
    }
    int compressor_find(int x){
        if(parent[x]==x) return x;
        return parent[x]= compressor_find(parent[x]);
    }
    int normal_find(int x){
        if(parent[x]==x) return x;
        return normal_find(parent[x]);
    }

    bool find_cycles(vector<pair<int, int>> & edges, int k_edges){
        for(int i=0; i<k_edges; i++){
            int x= edges[i].first;
            int y= edges[i].second;
            x= normal_find(x);
            y= normal_find(y);
            if(x==y){
                return true;
            }
            else{
                if(size[x]>=size[y]){
                    size[x]+=size[y];
                    parent[y]=x;

                }
                else{
                    size[y]+=size[x];
                    parent[x]=y;
                }
            }
        }
        return false;
    }
    void onion(int x, int y){
        x= compressor_find(x);
        y= compressor_find(y);
        if(x!=y){
            if(size[x]>=size[y]){
                // mp[size[y]].erase(y);     (#1)
                // mp[size[x]].erase(x);     (#1)
                parent[y]=x;
                size[x]+=size[y];
                // mp[size[x]].insert(x);     (#1)
            }
            else{
                // mp[size[y]].erase(y);     (#1)
                // mp[size[x]].erase(x);     (#1)
                parent[x]=y;
                size[y]+=size[x];
                // mp[size[y]].insert(y);     (#1)
            }
        }
    }
};


// make a tree clean but usually there is no need as this would require a complete bfs, try to think other way
void cleaner(vector<vector<int>> &v, vector<int>& par, int n){
    queue<int> q;
    q.push(1);
    par[1]=1;
    vector<bool> visited(n+1, 0);
    while(q.empty()!=1){
        int cur= q.front();
        q.pop();
        visited[cur]=1;
        for(int i=0; i<v[cur].size(); i++){
            int j= v[cur][i]; 
            if(!visited[j]){
                par[j]=cur;
                q.push(j);
            }
        }
    }
}

// this dfs find depth of a particular node as well as size of the subtree attached to a particular node
ll depthu_and_sizeu(ll cur, vector<bool>& visited, ll depth, vector<vector<ll>> &v, vector<ll>& dpt, vector<ll>& st){
    visited[cur]=1;
    dpt[cur]= depth;
    for(int i=0; i<v[cur].size(); i++){
        ll j= v[cur][i];
        if(!visited[j]){
            st[cur]+= depthu_and_sizeu(j, visited, depth+1, v, dpt, st);
        }
    }
    return st[cur];
} 





//PRIYANSH LAZY SEGMENT TREE TEMPLATE COULD BE USEFULL IN THE FUTURE
template<typename Node, typename Update>
struct LazySGT {
    vector<Node> tree;
    vector<bool> lazy;
    vector<Update> updates;
    vector<ll> arr; // type may change
    int n;
    int s;
    LazySGT(int a_len, vector<ll> &a) { // change if type updated
        arr = a;
        n = a_len;
        s = 1;
        while(s < 2 * n){
            s = s << 1;
        }
        tree.resize(s); fill(all(tree), Node());
        lazy.resize(s); fill(all(lazy), false);
        updates.resize(s); fill(all(updates), Update());
        build(0, n - 1, 1);
    }
    void build(int start, int end, int index) { // Never change this
        if (start == end)   {
            tree[index] = Node(arr[start], start);
            return;
        }
        int mid = (start + end) / 2;
        build(start, mid, 2 * index);
        build(mid + 1, end, 2 * index + 1);
        tree[index].merge(tree[2 * index], tree[2 * index + 1]);
    }
    void pushdown(int index, int start, int end){
        if(lazy[index]){
            int mid = (start + end) / 2;
            apply(2 * index, start, mid, updates[index]);
            apply(2 * index + 1, mid + 1, end, updates[index]);
            updates[index] = Update();
            lazy[index] = 0;
        }
    }
    void apply(int index, int start, int end, Update& u){
        if(start != end){
            lazy[index] = 1;
            updates[index].combine(u, start, end);
        }
        u.apply(tree[index], start, end);
    }
    void update(int start, int end, int index, int left, int right, Update& u) {  // Never Change this
        if(start > right || end < left)
            return;
        if(start >= left && end <= right){
            apply(index, start, end, u);
            return;
        }
        pushdown(index, start, end);
        int mid = (start + end) / 2;
        update(start, mid, 2 * index, left, right, u);
        update(mid + 1, end, 2 * index + 1, left, right, u);
        tree[index].merge(tree[2 * index], tree[2 * index + 1]);
    }
    Node query(int start, int end, int index, int left, int right) { // Never change this
        if (start > right || end < left)
            return Node();
        if (start >= left && end <= right){
            pushdown(index, start, end);
            return tree[index];
        }
        pushdown(index, start, end);
        int mid = (start + end) / 2;
        Node l, r, ans;
        l = query(start, mid, 2 * index, left, right);
        r = query(mid + 1, end, 2 * index + 1, left, right);
        ans.merge(l, r);
        return ans;
    }
    void make_update(int left, int right, ll val) {  // pass in as many parameters as required
        Update new_update = Update(val); // may change
        update(0, n - 1, 1, left, right, new_update);
    }
    Node make_query(int left, int right) {
        return query(0, n - 1, 1, left, right);
    }
};
struct Node1 {
    ll val; // may change
    int index;
    Node1() { // Identity element
        val = INF;    // may change
        index = -1;
    }
    Node1(ll p1, int index1) {  // Actual Node
        val = p1; // may change
        index = index1;
    }
    void merge(Node1 &l, Node1 &r) { // Merge two child nodes
        if(l.val < r.val){
            index = l.index;
            val = l.val;
        }else{
            index = r.index;
            val = r.val;
        }
    }
};
struct Update1 {
    ll val; // may change
    Update1(){ // Identity update
        val = 0;
    }
    Update1(ll val1) { // Actual Update
        val = val1;
    }
    void apply(Node1 &a, int start, int end) { // apply update to given node
        a.val += val; // may change
    }
    void combine(Update1& new_update, int start, int end){
        val += new_update.val;
    }
};



struct seg_tree{
    int n, nextpot; 
    vector<int> seg_t;
    seg_tree(int k){
        n=k; 
        nextpot= pow(2, ceil((double)log2(k)));
        seg_t.resize(2*nextpot+10);
    }
    void take_intput(int size){
        for(int i=nextpot, j=1; j<=size; j++, i++) cin>>seg_t[i];
    }
    void build(){
        for(int i=2*nextpot-1; i>1; i-=2){
            seg_t[i/2]= max(seg_t[i], seg_t[i-1]);
        }
    }
    void update(int position, int value){
        position+= nextpot-1;
        seg_t[position]=value;
        while(position!=1){
            seg_t[position/2]= max(seg_t[position], position&1? seg_t[position-1]: seg_t[position+1]);
            position/=2;
        }
    }
    void query(int query_l, int query_r, int cur_node, int cur_node_l, int cur_node_r, int &value){

        if(cur_node_l > query_r or cur_node_r < query_l ) return;

        if(cur_node_l>=query_l and cur_node_r<= query_r){
            value= max(value, seg_t[cur_node]);
            return;
        }
        else{
            int len= cur_node_r - cur_node_l +1;
            query(query_l, query_r, cur_node*2, cur_node_l, cur_node_l + len/2 -1, value);

            query(query_l, query_r, cur_node*2+1, cur_node_l+ len/2, cur_node_r, value);
        }
        return;
    }
}



struct fwt{
    int n; vector<int> bit;
    fwt(int k){
        n=k;
        bit.resize(k+1, 0);
    }
    void update(int start, int diff){ //diff with what was already there in original array
        if(start==0) return;
        while(start<=n){
            bit[start]+= diff;
            start+= start&(-1*start);
        }
    }
    // remember i&(-i) gives us last set bit
    int prefix(int pos){
        int sum=0;
        while(pos>0){
            sum+= bit[pos];
            pos-= pos& (-1*pos);
        }
        return sum;
    }
    int query(int l, int r){
        return prefix(r)-prefix(l-1);
    }
}


//DUAL SEGMENT TREE
struct dual_segment_tree{
    int N;
    vector<T> ST;
    dual_segment_tree(vector<T> A){
        int n=A.size();
        N = 1;
        while(N<n){
            N*=2;
        }
        ST=vector<T>(N*2-1,0);
        for (int i=0; i<n; i++){
            ST[N-1+i]= A[i];
        }
    }
    T operator [](int k){
        k+=N-1;
        T ans=ST[k];
        while(k > 0){
            k=(k-1)/2;
            ans+=ST[k];
        }
        return ans;
    }
    void range_add(int L, int R, T x, int i, int l, int r){
        if(R<=l || r<=L){
            return;
        } else if (L<=l && r<=R){
            ST[i] += x;
            return;
        } else {
            int m= (l+r)/2;
            range_add(L, R, x, i*2+1, l, m);
            range_add(L, R, x, i*2+2, m, r);
            return;
        }
    }
    void range_add(int L, int R, T x){
        range_add(L, R, x, 0, 0, N);
    }
};



boo rabin_miller_helper(ll base, ll n, ll d){
    ll x= expo_mania(base, d, n);
    if(x==1 or x==n-1) return true;

    while(d!=n-1){
        d*=2;
        x= (x*x)%n;
        if(x==1) return false;
        if(x==n-1) return true;
    }
}

bool rabin_miller_primality_test(ll n){
    if(n<=1 or (n%2==0 and n!=2)){ return false; }

    vector<ll> base= {2, 3, 5, 7, 11, 13, 17, 19, 23, 29};
    for(int i=0; i<10; i--){
        if(n== base[i]) return true;
    }

    ll d= n-1;
    while(d%2==0) d/=2;

    for(int i=0; i<10; i++){
        if(rabin_miller_helper(base[i], n, d) == false) return false; //its composite
    }
    return true; // its prime

}



int main() {
    GODSPEED_SPIDERMAN;
    auto start= high_resolution_clock::now();


    OH_oh(t);
    // DRIVER FUNTION
    pair<ll, ll> kk= extended_gcd(6, 7);
    cout<<kk.first<<" "<<kk.second<<endl;


    auto stop= high_resolution_clock::now();

    auto duration= duration_cast<microseconds>(stop-start);
    cout<<duration.count()<<endl;

}   
