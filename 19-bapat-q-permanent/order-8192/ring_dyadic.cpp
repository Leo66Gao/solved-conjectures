/* Hardware-floating-point-independent verifier of an upper bound for
   ||P||_F^2/n!.  All arithmetic that determines the bound is integer.
   GCC or Clang with unsigned __int128.  Same input/output as ring_interval.cpp.
   Each nonzero value is represented as m*2^e, 2^55<=m<2^56.
   Addition/multiplication/reciprocal are rounded outward by integer shifts.
*/
#include <cstdint>
#include <vector>
#include <iostream>
#include <stdexcept>
#include <algorithm>
#include <limits>
using namespace std;using U=uint64_t;using B=__uint128_t;
constexpr U LO=U(1)<<55,HI=U(1)<<56;
void req(bool p,const char*s){if(!p)throw runtime_error(s);}
struct D{U m=0;int e=0;};
D normalize(U m,int e,bool up){
 if(!m)return {};while(m>=HI){m=(m+(up && (m&1)))/2;++e;} // only used when m fits and is small
 while(m<LO){m<<=1;--e;}return {m,e};
}
D integer(U x,int e=0,bool up=true){
 if(!x)return {};int bits=64-__builtin_clzll(x);int k=bits-56;
 if(k>0){U r=x>>k;if(up&&(x&((U(1)<<k)-1)))++r;return normalize(r,e+k,up);}
 return {x<<(-k),e+k};
}
inline D add(D a,D b){
 if(!a.m)return b;if(!b.m)return a;if(a.e<b.e)swap(a,b);int k=a.e-b.e;
 U x=k>=64?1:(k==0?b.m:((b.m>>k)+bool(b.m&((U(1)<<k)-1))));
 U s=a.m+x;int e=a.e;if(s>=HI){s=(s+1)>>1;++e;}return {s,e};
}
inline D mul(D a,D b,bool up=true){
 if(!a.m||!b.m)return {};B p=(B)a.m*b.m;int k=p>=(B(1)<<111)?56:55;
 U q=U(p>>k);if(up&&(p&((B(1)<<k)-1)))++q;int e=a.e+b.e+k;
 if(q>=HI){q=(q+1)>>1;++e;}return {q,e};
}
D recip(D a){req(a.m!=0,"zero reciprocal");B t=B(1)<<111;U q=U(t/a.m);if(t%a.m)++q;return normalize(q,-a.e-111,true);}
D dyadic_ratio(U a,U b){return mul(integer(a),recip(integer(b,0,false)));}
U sqrt_floor(unsigned k){B x=(B)k<<80;U l=0,h=U(1)<<48;while(l+1<h){U c=l+(h-l)/2;if((B)c*c<=x)l=c;else h=c;}req((B)l*l<=x&&(B)(l+1)*(l+1)>x,"sqrt check");return l;}
U ceil_scaled(D d,int k){if(!d.m)return 0;int e=d.e+k;if(e>=0){req(e<8&&d.m<=(UINT64_MAX>>e),"output overflow");return d.m<<e;}int s=-e;if(s>=64)return 1;return (d.m>>s)+bool(d.m&((U(1)<<s)-1));}
int main(){try{
 int m,N;req(bool(cin>>m>>N),"header");req(m>=4&&m%4==0&&m<=64&&N>=1&&N<=5000&&m*N<65536,"size");int n=m*N;
 vector<U> an(N),ad(N);for(int t=0;t<N;t++){req(bool(cin>>an[t]>>ad[t]),"radius");req(ad[t]>0,"denominator");}
 D one=integer(1);vector<D> rl(n+1),ru(n+1);for(int i=1;i<=n;i++){U a=sqrt_floor(i);rl[i]=integer(a,-40,false);ru[i]=integer(a+1,-40);}
 vector<D> dn(N);for(int t=0;t<N;t++){D lo=one;for(int h=1;h<=m;h++)lo=mul(lo,rl[t*m+h],false);dn[t]=recip(lo);}
 vector<vector<D>> f(m+1,vector<D>(n+1,one));for(int k=1;k<=m;k++)for(int j=0;j<=n-k;j++)f[k][j]=mul(f[k-1][j],ru[j+k]);
 vector<U> co(m/2+1);co[0]=1;for(int j=1;j<=m/2;j++){B p=(B)co[j-1]*(m-2*j+2)*(m-2*j+1);U q=j*(m-j);req(p%q==0&&p/q<=UINT64_MAX,"ring coefficient");co[j]=p/q;}
 vector<D> p(1,one);vector<size_t> off(n+2),off2(n+2);
 auto offsets=[&](int d,vector<size_t>&o){size_t z=0;for(int a=0;a<=d;a++){o[a]=z;int b0=a%m;if(b0<=d-a)z+=(d-a-b0)/m+1;}o[d+1]=z;return z;};offsets(0,off);
 for(int t=0;t<N;t++){
  int d=t*m;vector<D> q(offsets(d+m,off2));D a2=dyadic_ratio(an[t],ad[t]);vector<D> powa(m/2+1,one),c(m/2+1);for(int h=1;h<=m/2;h++)powa[h]=mul(powa[h-1],a2);
  for(int h=0;h<=m/2;h++)c[h]=mul(mul(integer(co[h]),powa[m/2-h]),dn[t]);
  for(int a=0;a<=d;a++){
   int b0=a%m;size_t ix=off[a];if(b0>d-a)continue;D xa=mul(dn[t],f[m][a]);D ca[33];for(int h=0;h<=m/2;h++)ca[h]=mul(c[h],f[h][a]);
   for(int b=b0;b<=d-a;b+=m,ix++){
    D v=p[ix];if(!v.m)continue;int k=d-a-b;size_t j=(b-b0)/m;
    q[off2[a+m]+j]=add(q[off2[a+m]+j],mul(v,xa));q[off2[a]+j+1]=add(q[off2[a]+j+1],mul(mul(v,dn[t]),f[m][b]));
    for(int h=0;h<=m/2;h++){if(!ca[h].m)continue;size_t dest=off2[a+h]+(b+h)/m;D x=mul(mul(mul(v,ca[h]),f[h][b]),f[m-2*h][k]);q[dest]=add(q[dest],x);}
   }
  }
  p.swap(q);off.swap(off2);if((t+1)%64==0||t+1==N)cerr<<"rings "<<t+1<<"/"<<N<<" slots "<<p.size()<<"\n";
 }
 D sum{};for(D v:p)sum=add(sum,mul(v,v));cout<<ceil_scaled(sum,40)<<" "<<(U(1)<<40)<<"\n";return 0;
 }catch(const exception&e){cerr<<"ERROR: "<<e.what()<<"\n";return 1;}}
