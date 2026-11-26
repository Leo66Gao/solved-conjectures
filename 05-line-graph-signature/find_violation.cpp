// Exact rank-budget-1 decision for Paone--Paone through c=7.
// Reads degree/edge-list output of cubic_kernels.py. Standard C++17.
#include <iostream>
#include <vector>
#include <array>
#include <map>
#include <algorithm>
#include <numeric>
#include <cassert>
#include <cstdint>
#include <stdexcept>
using namespace std;
using I=__int128_t;
const int M=12;
using A=array<array<I,M>,M>;
static I mul(I x,I y){I z;if(__builtin_mul_overflow(x,y,&z))throw overflow_error("int128 multiplication");return z;}
static I sub(I x,I y){I z;if(__builtin_sub_overflow(x,y,&z))throw overflow_error("int128 subtraction");return z;}
static I ab(I x){return x<0 ? sub(0,x):x;}
static I gc(I a,I b){while(b){I c=a%b;a=b;b=c;}return a;}

static bool psd_rank_at_least(A a,int n,int need){
    // A feasible matrix has signature >= need >= n-1, so it must be PSD.
    const int orig=n;
    for(int k=0;k<n;k++){
        int p=-1;
        for(int i=k;i<n;i++){if(a[i][i]<0)return false;if(a[i][i]>0&&p<0)p=i;}
        if(p<0){
            for(int i=k;i<n;i++)for(int j=i+1;j<n;j++)if(a[i][j])return false;
            return k>=need;
        }
        swap(a[p],a[k]);for(int i=0;i<n;i++)swap(a[i][p],a[i][k]);
        // Positive factor times the exact Schur complement, then common gcd.
        I g=0;
        for(int i=k+1;i<n;i++)for(int j=i;j<n;j++){
            a[i][j]=sub(mul(a[k][k],a[i][j]),mul(a[i][k],a[k][j]));
            g=gc(g,ab(a[i][j]));
        }
        if(!g)g=1;
        for(int i=k+1;i<n;i++)for(int j=i;j<n;j++)a[j][i]=a[i][j]/=g;
    }
    return orig>=need;
}
int root(vector<int>&p,int i){while(p[i]!=i)i=p[i];return i;}

int main(){
 int c;if(!(cin>>c))return 1;
 int n,m;uint64_t states=0, all=0;map<int,int> counts;
 int limit=(3*c-1)/2, need=limit+1;
 while(cin>>n>>m){
   assert(n<=M&&m==n+c-1);counts[n]++;all++;
   array<int,M> d{};for(int i=0;i<n;i++)cin>>d[i];
   vector<pair<int,int>> e(m);
   for(auto&[u,v]:e)cin>>u>>v;
   if(n<need)continue;
   int delta=n-need;assert(delta>=0&&delta<=1);
   vector<int> p(n);iota(p.begin(),p.end(),0);
   vector<int> signs(m,-1);int free=0;
   map<pair<int,int>,vector<int>> groups;
   for(int i=0;i<m;i++){
      auto [u,v]=e[i];groups[e[i]].push_back(i);
      if(u==v)continue;
      if(root(p,u)!=root(p,v))p[root(p,u)]=root(p,v);
      else signs[i]=free++;
   }
   assert(root(p,0)==root(p,n-1));assert(free<=c);
   vector<tuple<int,int,int>> moves{{-1,-1,0}};
   if(delta)for(auto&[uv,is]:groups){
       auto [u,v]=uv;
       if(u==v) {
          // Connected kernels here have at most one loop at a vertex.
          assert(is.size()==1);moves.push_back({u,v,1<<is[0]});
       } else for(int mask=1;mask<(1<<(int)is.size());mask++){
          int s=0;for(int j=0;j<(int)is.size();j++)if(mask>>j&1)s|=1<<is[j];
          moves.push_back({u,v,s});
       }
   }
   for(int sb=0;sb<(1<<free);sb++){
      auto sg=[&](int i){return signs[i]>=0&&(sb>>signs[i]&1)?-1:1;};
      for(auto [x,y,mask]:moves){
          int n2=n-(mask!=0);
          int f=0;
          for(int i=0;i<m;i++)if(mask>>i&1){
             if(!f)f=sg(i);else if(f!=sg(i)){f=2;break;}
          }
          if(f==2)continue; // Opposite constraints have rank two.
          array<int,M> v2{},factor{};int idx=0;
          for(int i=0;i<n;i++){
             if(i==y)continue;
             v2[i]=idx++;factor[i]=1;
          }
          if(mask&&x!=y){v2[y]=v2[x];factor[y]=-f;}
          if(mask&&x==y)factor[y]=0;
          assert(idx==n2);
          A base{};
          auto add=[&](int u,int v,int s){if(factor[u]&&factor[v])base[v2[u]][v2[v]]+=s*factor[u]*factor[v];};
          for(int i=0;i<n;i++)add(i,i,d[i]-2);
          for(int i=0;i<m;i++)if(!(mask>>i&1)){
             auto [u,v]=e[i];add(u,v,sg(i));add(v,u,sg(i));
          }
          for(int leaf=-1;leaf<(delta&&!mask ? n:0);leaf++){
              A a=base;int pneed=need+(leaf>=0);
              if(leaf>=0)a[v2[leaf]][v2[leaf]]+=2;
              states++;
              if(psd_rank_at_least(a,n2,pneed)){
                  cerr<<"VIOLATION c="<<c<<" n="<<n<<" signs="<<sb<<" constraints="<<mask<<" leaf="<<leaf<<'\n';
                  for(auto [u,v]:e)cerr<<u<<','<<v<<' ';
                  cerr<<'\n';
                  return 2;
              }
          }
      }
   }
 }
 cout<<"c="<<c<<" exact kernel counts by n:";
 for(auto [a,b]:counts)cout<<" "<<a<<":"<<b;
 cout<<"; candidate states checked="<<states<<"; no violation\n";
}
