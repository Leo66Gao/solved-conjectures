// Exhaustive separate ternary check, n=3*5-1. A 64-bit additive signature is
// used ONLY for bucketing; candidate equality is decided by complete exact data.
#include <algorithm>
#include <array>
#include <cstdint>
#include <iostream>
#include <map>
#include <set>
#include <stdexcept>
#include <vector>
using namespace std;
using u64=uint64_t; using Word=array<unsigned char,14>;
u64 mix(u64 z){z+=0x9e3779b97f4a7c15ULL;z=(z^(z>>30))*0xbf58476d1ce4e5b9ULL;z=(z^(z>>27))*0x94d049bb133111ebULL;return z^(z>>31);}
using Sig = array<unsigned char,3375>;
size_t slot(int a,int b,int c){return 225*a+15*b+c;}
Word decode(int w){Word a;for(auto&c:a){c=w%3;w/=3;}return a;}
int encode(Word a){int w=0;for(int i=13;i>=0;i--)w=3*w+a[i];return w;}
Sig exact(Word a){Sig s{};for(int i=0;i<14;i++){int cnt[3]={};for(int j=i;j<14;j++){cnt[a[j]]++;s[slot(cnt[0],cnt[1],cnt[2])]++;}}return s;}
set<int> predicted(Word w){set<int> out={encode(w)};Word z=w;reverse(z.begin(),z.end());out.insert(encode(z));
for(int p:{3,5}){bool block=true;
 for(int r=1;r<=14;r++)if(r%p && w[r-1]!=w[(r%p)-1])block=false;
 if(!block)continue;
 for(int a:{0,1})for(int b:{0,1}){Word t=w;for(int r=1;r<=14;r++){
 if(r%p && a)t[r-1]=w[(p-r%p)-1];
 if(!(r%p)&& b)t[r-1]=w[14-r];
 }out.insert(encode(t));}
}return out;}
int main(){const int lim=4782969;u64 lut[3375];for(int i=0;i<3375;i++)lut[i]=mix(i);
vector<pair<u64,int>> v;v.reserve(lim);
for(int i=0;i<lim;i++){Word w=decode(i);u64 h=0;for(int k=0;k<14;k++){int cnt[3]={};for(int j=k;j<14;j++){cnt[w[j]]++;h+=lut[slot(cnt[0],cnt[1],cnt[2])];}}v.emplace_back(h,i);}
sort(v.begin(),v.end());map<int,int>hist;
for(size_t i=0,j;i<v.size();i=j){for(j=i+1;j<v.size()&&v[j].first==v[i].first;j++);
 // Match full histogram before declaring words equivalent.
 vector<bool>used(j-i);for(size_t a=i;a<j;a++)if(!used[a-i]){
 set<int> eq={v[a].second};used[a-i]=true;auto S=exact(decode(v[a].second));
 for(size_t b=a+1;b<j;b++)if(!used[b-i] && exact(decode(v[b].second))==S) {used[b-i]=true;eq.insert(v[b].second);}
 for(int x:eq)if(predicted(decode(x))!=eq)throw runtime_error("counterexample");
 hist[eq.size()]++;
 }}
cout<<"alphabet=3 length=14 words="<<lim<<" classes:";for(auto[k,n]:hist)cout<<" size"<<k<<"="<<n;cout<<" all class memberships match\n";}
