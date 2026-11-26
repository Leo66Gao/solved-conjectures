// Independent bitmask implementation for D7; AI-assisted, Leo Gao.
#include <iostream>
#include <vector>
#include <algorithm>
using namespace std;
int main(){const int k=7; vector<pair<int,int>> e;for(int i=0;i<k;i++)for(int j=i+1;j<k;j++)e.push_back({i,j});
int a=0,b=0,c=0;
for(int mask=0;mask<(1<<e.size()); mask++){int d[k]={},r0=0,n=0;
for(unsigned l=0;l<e.size();l++)d[(mask>>l&1)?e[l].first:e[l].second]++;
for(unsigned l=0;l<e.size();l++){int i=e[l].first,j=e[l].second;if(mask>>l&1)swap(i,j);r0+=max(d[i],d[j]);if(d[j]>d[i])n++;}
a=max(a,r0);b=max(b,3*r0-2*n);c=max(c,r0-n);}
cout<<"all "<<(1<<e.size())<<" tournaments in D7: L(0)="<<2*a<<", 3L(2/3)="<<2*b<<", L(1)="<<2*c<<"\n";
return !(2*a==182 && 2*b==462 && 2*c==144);}
