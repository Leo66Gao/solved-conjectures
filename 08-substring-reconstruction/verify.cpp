#include <algorithm>
#include <array>
#include <cassert>
#include <cstdint>
#include <iostream>
#include <map>
#include <set>
#include <stdexcept>
#include <string>
#include <vector>
// Exhaustive and collision safe. Only the sorting prefilter uses a hash.
using namespace std;
using u32=uint32_t; using u64=uint64_t;
using Sig=array<unsigned char,276>; // n<=21, 2+3+...+(n+1)<=252
Sig sig(u32 w,int n){
  Sig s{}; int weights[23]={};
  for(int i=0;i<n;i++)weights[i+1]=weights[i]+((w>>i)&1);
  for(int len=1,offset=0;len<=n;offset+=len+1,len++)
    for(int i=0;i+len<=n;i++)s[offset+weights[i+len]-weights[i]]++;
  return s;
}
u64 hash_sig(const Sig&s) {u64 h=14695981039346656037ull;for(auto c:s)h=(h^c)*1099511628211ull;return h;}
u32 rev(u32 w,int n){u32 x=0;while(n--){x=(x<<1)|(w&1);w>>=1;}return x;}
u32 inter(u32 u,u32 v,int p,int q){
  u32 w=0; for(int k=0;k<q;k++){w|=u<<(k*p);
    if(k<q-1)w|=((v>>k)&1)<<(k*p+p-1);}
  return w;
}
void check(int p,int q){
 const int n=p*q-1; if(n>21)throw runtime_error("n>21");
 map<u32,set<u32>> expected;
 for(int order=0;order<2;order++,swap(p,q))
 for(u32 u=0;u<(1u<<(p-1));u++)
 for(u32 v=0;v<(1u<<(q-1));v++){
   u32 U=rev(u,p-1),V=rev(v,q-1);
   if(U==u||V==v)continue;
   auto w=inter(u,v,p,q);
   expected[w]={w,inter(U,v,p,q),inter(u,V,p,q),inter(U,V,p,q)};
 }
 vector<pair<u64,u32>> keys; keys.reserve(1u<<n);
 for(u32 w=0;w<(1u<<n);w++)keys.emplace_back(hash_sig(sig(w,n)),w);
 sort(keys.begin(),keys.end());map<int,int> hist; int seen=0;
 for(size_t i=0,j;i<keys.size();i=j){
   for(j=i+1;j<keys.size()&&keys[j].first==keys[i].first;j++);
   map<Sig,set<u32>> exact;
   for(size_t k=i;k<j;k++)exact[sig(keys[k].second,n)].insert(keys[k].second);
   for(auto &[signature,words]:exact){
     hist[words.size()]++;
     for(auto w:words){
       set<u32> default_set={w,rev(w,n)};
       auto it=expected.find(w);bool ambiguous=it!=expected.end();
       if((ambiguous?it->second:default_set)!=words)throw runtime_error("counterexample");
       if(ambiguous)seen++;
     }
   }
 }
 if(size_t(seen)!=expected.size())throw runtime_error("missing records");
 cout<<"p="<<p<<" q="<<q<<" length="<<n<<" words="<<(1u<<n)<<" classes:";
 for(auto [k,v]:hist)cout<<" size"<<k<<"="<<v;
 cout<<" ambiguous words="<<seen<<" all class memberships match\n";
}
int main(){check(3,5);check(3,7);}
