// Exact finite-boundary probability for the rational resonance c=1 (p=q^2).
// Build: c++ -O3 -std=c++17 resonance.cpp -o resonance && ./resonance 9
#include <algorithm>
#include <array>
#include <cstdint>
#include <cstdlib>
#include <iomanip>
#include <iostream>
#include <vector>
using namespace std;
int main(int argc,char**argv) {
 int K=argc>1?atoi(argv[1]):9;
 if(K<1||K>10) {cerr<<"Use 1 <= K <= 10.\n";return 1;}
 const int L=1<<K;
 // x=phi satisfies x*x=x+1. Store u+v*x as u+v*2^24.
 // For ell<=10, each coordinate sum is <=10*F_20=67650,
 // so this encoding is also injective when comparing sums of two differences.
 const int64_t B=int64_t(1)<<24; array<int64_t,21> f{};
 f[0]=1;f[1]=B;for(int i=2;i<=2*K;i++)f[i]=f[i-1]+f[i-2];
 vector<vector<int64_t>> table(L,vector<int64_t>(L));
 for(int a=0;a<L;a++) for(int e=0;e<L;e++) for(int k=1;k<=K;k++) {
    int x=a>>(K-k);
    if(x==(e&((1<<k)-1))) table[a][e]+=f[k+__builtin_popcount(unsigned(x))];
 }
 uint64_t total=0;
 vector<int64_t> dif(L);
 for(int a=0;a<L;a++) for(int b=a;b<L;b++){
    for(int e=0;e<L;e++)dif[e]=table[b][e]-table[a][e];
    sort(dif.begin(),dif.end());
    int i=0,j=L-1; uint64_t pairs=0;
    while(i<L && j>=0){
       auto s=dif[i]+dif[j];
       if(s<0){i++;continue;} if(s>0){j--;continue;}
       int ni=i+1,nj=j-1;
       while(ni<L && dif[ni]==dif[i])ni++;
       while(nj>=0 && dif[nj]==dif[j])nj--;
       pairs+=uint64_t(ni-i)*(j-nj);i=ni;j=nj;
    }
    total+=(a==b?1:2)*pairs;
 }
 uint64_t den=uint64_t(1)<<(4*K);
 cout<<"K="<<K<<" z_K="<<total<<"/"<<den<<" = "<<setprecision(12)<<double(total)/den
     <<"  rigorous |z-z_K| <= "<<4./L<<"\n";
}
