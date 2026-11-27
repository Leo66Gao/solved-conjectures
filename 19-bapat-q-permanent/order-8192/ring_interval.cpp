/* Outward-rounded upper bound for ||P||_F^2 / n! for a product of
   half-step angular rings.  All coefficient updates are nonnegative.
   Compile: g++ -O3 -std=c++17 -frounding-math -ffp-contract=off -fno-fast-math ring_interval.cpp -o ring_interval
   Requires IEC 60559 binary floating point, working directed rounding,
   and a compiler respecting -frounding-math (GCC on x86-64 tested).
   Inputs: m N, followed by N pairs of positive integers num den (a^2).
   Output: dyadic numerator and denominator of an upper bound.
   No sqrt/log/pow/transcendental floating functions enter the bound.
*/
#include <vector>
#include <cstdint>
#include <cfenv>
#include <cmath>
#include <iostream>
#include <iomanip>
#include <limits>
#include <stdexcept>
#include <algorithm>
#include <cassert>
#pragma STDC FENV_ACCESS ON
using namespace std;
using ld=long double;
using u128=__uint128_t;
using u64=uint64_t;
void require(bool ok,const char* why){if(!ok)throw runtime_error(why);}
void rounding(int mode){require(fesetround(mode)==0,"fesetround failed");require(fegetround()==mode,"rounding mode mismatch");}
// Certified sqrt(k) enclosure on the mesh 2^-40, using only integers.
u64 root_floor(unsigned k){u128 x=(u128)k<<80;u64 a=0,b=1ULL<<48;while(a+1<b){u64 c=a+(b-a)/2;if((u128)c*c<=x)a=c;else b=c;}require((u128)a*a<=x && (u128)(a+1)*(a+1)>x,"integer sqrt");return a;}
int main(){try{
 require(numeric_limits<ld>::is_iec559 && numeric_limits<ld>::radix==2 && numeric_limits<ld>::digits>=64,"need IEC binary long double >=64-bit significand");
 // Test runtime behavior including addition, multiplication and division.
 volatile ld one=1,half_ulp=0x1p-64L,two=2,three=3;
 rounding(FE_UPWARD);volatile ld u=one+half_ulp,du=one/three,mu=u*u;
 rounding(FE_DOWNWARD);volatile ld l=one+half_ulp,dl=one/three,ml=u*u;
 require(u>one && l==one && du>dl && mu>ml,"directed arithmetic self-test failed");
 int m,N;require(bool(cin>>m>>N),"input header");require(m>=4 && m%4==0 && m<=64 && N>=1 && N<=5000 && m*N<65536,"invalid size");
 int n=m*N;vector<u64> an(N),ad(N);for(int t=0;t<N;t++){require(bool(cin>>an[t]>>ad[t]),"input radius");require(ad[t]>0,"zero denominator");}
 vector<u64> sf(n+1);for(int i=1;i<=n;i++)sf[i]=root_floor(i);
 // Downward product lower bounds for sqrt((d+m)!/d!), d=m*t.
 vector<ld> denom(N,1);rounding(FE_DOWNWARD);
 for(int t=0;t<N;t++)for(int h=1;h<=m;h++)denom[t]*=ld(sf[m*t+h])*0x1p-40L;
 // Upward products for sqrt((j+k)!/j!).
 rounding(FE_UPWARD);vector<vector<ld>> f(m+1,vector<ld>(n+1,1));
 for(int k=1;k<=m;k++)for(int j=0;j<=n-k;j++)f[k][j]=f[k-1][j]*(ld(sf[j+k]+1)*0x1p-40L);
 vector<u64> co(m/2+1);co[0]=1;
 for(int j=1;j<=m/2;j++){u128 num=(u128)co[j-1]*(m-2*j+2)*(m-2*j+1);u64 den=j*(m-j);require(num%den==0 && num/den<=UINT64_MAX,"integer coefficient overflow");co[j]=num/den;}
 // q[a,b] only if a-b == 0 mod m; third exponent is d-a-b.
 vector<ld> p(1,1);vector<size_t> off(n+2),off2(n+2);
 auto offsets=[&](int d,vector<size_t>&o){size_t z=0;for(int a=0;a<=d;a++){o[a]=z;int b0=a%m;if(b0<=d-a)z+=(d-a-b0)/m+1;}o[d+1]=z;return z;};
 offsets(0,off);
 for(int t=0;t<N;t++){
  int d=t*m;vector<ld> q(offsets(d+m,off2),0);ld dn=1/denom[t], a2=ld(an[t])/ld(ad[t]);
  // all powers are integral powers of the rational a^2
  vector<ld> powa(m/2+1,1),c(m/2+1);for(int h=1;h<=m/2;h++)powa[h]=powa[h-1]*a2;
  for(int h=0;h<=m/2;h++)c[h]=ld(co[h])*powa[m/2-h]*dn;
  for(int a=0;a<=d;a++){
   int b0=a%m;size_t ix=off[a];if(b0>d-a)continue;
   ld xa=dn*f[m][a];
   for(int b=b0;b<=d-a;b+=m,ix++){
    ld v=p[ix];if(v==0)continue;int k=d-a-b;size_t j=(b-b0)/m;
    q[off2[a+m]+j]+=v*xa;
    q[off2[a]+j+1]+=v*dn*f[m][b];
    for(int h=0;h<=m/2;h++){
     if(c[h]==0)continue;size_t dest=off2[a+h]+(b+h)/m;
     q[dest]+=v*c[h]*f[h][a]*f[h][b]*f[m-2*h][k];
    }
   }
  }
  p.swap(q);off.swap(off2);
  // A nonfinite bound can never be used as a certificate.
  if((t+1)%64==0 || t+1==N){ld mx=*max_element(p.begin(),p.end());require(isfinite(mx),"nonfinite coefficient bound");cerr<<"rings "<<t+1<<"/"<<N<<" slots "<<p.size()<<" max "<<setprecision(10)<<mx<<"\n";}
 }
 ld sum=0;for(ld v:p){require(v>=0&&isfinite(v),"invalid interval");sum+=v*v;}
 require(isfinite(sum)&&sum<0x1p20L,"norm overflow");
 // Multiplying by 2^40 is exact in binary here. ceil gives integer upper endpoint.
 ld s=ceil(sum*0x1p40L);require(s>=0&&s<0x1p63L,"output overflow");
 u64 U=(u64)s;cout<<U<<" "<<(1ULL<<40)<<"\n";
 cerr<<"norm upper bound = "<<setprecision(18)<<sum<<"; slots = "<<p.size()<<"\n";
 rounding(FE_TONEAREST);return 0;
 }catch(const exception&e){cerr<<"ERROR: "<<e.what()<<"\n";return 1;}}
