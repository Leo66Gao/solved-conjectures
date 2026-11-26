// All arithmetic is exact. g++ -O3 -std=c++17 verify-ten-quarter.cpp -o verify-ten-quarter
#include <algorithm>
#include <cassert>
#include <cstdint>
#include <iostream>
#include <cstdlib>
#include <vector>
using I=__int128_t;
using L=long long;
using P=std::pair<L,L>;
constexpr int n=10,N=1<<n,lim=44;
constexpr L Q=1LL<<50;
L cd(I a,I b){return (a+b-1)/b;}
std::vector<P> lg(1<<20);P l2;
int deg[n],lc[N],child[N][n],need[N],count,shape[lim],sums[lim+1],dep[lim+1],tmp[N];
int n_checked;
P lgs(L a,L b){
 assert(b<=a&&a<=2*b);
 L z=(I)Q*(a-b)/(a+b),h=cd((I)Q*(a-b),a+b);
 L A=(I)z*z/Q,B=cd((I)h*h,Q),lo=0,hi=0;
 for(int i=0;i<17;i++){lo+=2*z/(2*i+1);hi+=cd(2*h,2*i+1);z=(I)z*A/Q;h=cd((I)h*B,Q);}
 return {lo,hi+cd((I)2*h*Q,35*(Q-B))};
}
P Log(L a){if(a==1)return {0,0};L b=1LL<<(63-__builtin_clzll(a));int e=__builtin_ctzll(b);P v=lgs(a,b);return {v.first+e*l2.first,v.second+e*l2.second};}
L hhi,hlo;int mlim;
L margin=Q;int margin_m,margin_d;
void check(int m,int d){
 sums[m]++;if(m==16&&d==4)return;
 int A=29,G=20; // lambda=29/20
 int U=G*m,T=4*U+A*(m-16);if(m==lim)T=(4*G+A)*m;
 if(T<=0)return; // Nonpositive target: immediate by nonnegativity of J.
 I need=(I)T*l2.second+(I)(d*U-T)*(d*U>=T?hhi:hlo);
 L D=1LL<<(2*d);
 for(int i=0;i<(1<<d);i++)tmp[i]=0;
 for(int i=0;i<m;i++)tmp[shape[i]]=1;
 for(int j=1;j<(1<<d);j*=2)for(int i=0;i<(1<<d);i+=2*j)for(int k=i;k<i+j;k++){
   L a=tmp[k],b=tmp[k+j];tmp[k]=3*a+b;tmp[k+j]=a+3*b;
 }
 I up=0;L z=0;
 for (int i=0;i<(1<<d);i++){L w=tmp[i];assert(w>0&&w<=D&&w<(L)lg.size());z+=w;up+=(I)w*lg[w].second;}
 assert(z==m*D);
 I lower=(I)m*D*(2*d*l2.first+lg[m].first)-up;
 I diff=(lower*U-need*m*D);
 if(diff<=0){std::cerr<<"FAIL "<<m<<" "<<d<<" "<<(double)diff/(U*m*D*Q)<<"\n";exit(1);}
 // Uniform margin 12*2^-12 suffices for the reported p-neighborhood.
 assert(diff * (1<<12)>(I)12*U*m*D*Q);
 L g=diff/((I)U*m*D);if(g<margin)margin=g,margin_m=m,margin_d=d;
 n_checked++;
}
void dfs(int x,int depth){
 shape[depth-1]=x;
 if(depth==mlim){check(depth,shape[depth-1]?32-__builtin_clz(shape[depth-1]):0);return;}
 for(int i=0;i<lc[x];i++)--need[child[x][i]];
 for(int i=x+1;i<N;i++)if(need[i]==0)dfs(i,depth+1);
 for(int i=0;i<lc[x];i++)++need[child[x][i]];
}
int main(int argc,char**argv){
 l2=lgs(2,1);for(int i=1;i<(1<<20);i++)lg[i]=Log(i);
 hhi=cd((I)8*l2.second-3*lg[3].first,4);
 hlo=((I)8*l2.first-3*lg[3].second)/4;
 for(int x=1;x<N;x++){
   if(x&1)child[x-1][lc[x-1]++]=x,++need[x];
   for(int j=1;j<n;j++)if((x>>(j-1)&3)==2){int p=x-(1<<(j-1));child[p][lc[p]++]=x;++need[x];}
 }
 int low=argc>1?atoi(argv[1]):3, hi=argc>2?atoi(argv[2]):lim;
 for(mlim=low;mlim<=hi;mlim++){int mark=n_checked;dfs(0,1);std::cout<<"m="<<mlim<<" shapes="<<sums[mlim]<<" strict="<<n_checked-mark<<std::endl;}
 std::cout<<"minimum margin at least "<<margin<<"/"<<Q<<" nats (m="<<margin_m<<", d="<<margin_d<<")\n";
}
