#include <array>
#include <algorithm>
#include <cassert>
#include <iostream>
using namespace std;
using Order=array<int,128>;
int threshold; long long level[8]={}, hist[8][128]={}, visits7=0;
int code[64];
struct Extension {
 const Order &p;
 int k,n,full,single=-1;
 Order f{};
 int sign[729]={},best[65][65][2];
 explicit Extension(const Order& old,int atoms);
 void run(int lo,int hi);
};
int both(int a,int b,int full){return (!(a&b))+((a|b)==full);}
void use(const Order& p,int k){
 int count=0;
 for(int a=1;a<(1<<k);a++)count+=!(p[a-1]&p[a]);
 hist[k][count]++;level[k]++;
 if(k<7 && count==array<int,7>{0,1,2,4,7,13,22}[k]){cout<<"max "<<k<<" "<<count;for(int i=0;i<(1<<k);i++)cout<<" "<<p[i];cout<<"\n";}
 if(k==7){
   assert(count>=threshold);
   cout<<"leaf "<<count;for(int i=0;i<128;i++)cout<<" "<<p[i];cout<<"\n"; return;
 }
 Extension next(p,k+1);next.run(0,0);
}
Extension::Extension(const Order& old,int atoms):p(old),k(atoms),n(1<<(atoms-1)),full(2*n-1){
 for(int i=0;i<n;i++)if(p[i]==n/2)single=i;
 if(k<7)return;
 for(int i=n;i>=0;i--) for(int j=min(i,n-i);j>=0;j--)for(int t=0;t<2;t++){
  if((t?j:i)==0)continue;
  if(i+j==n){best[i][j][t]=1;continue;}
  int prev=t?n+p[j-1]:p[i-1];
  int h=both(prev,p[i],full)+best[i+1][j][0];
  if(j<i && i>single)h=max(h,both(prev,n+p[j],full)+best[i][j+1][1]);
  best[i][j][t]=h;
 }
}
void Extension::run(int lo,int hi){
 int h=lo+hi;
 if(h==n){use(f,k);return;}
 int M=full;
 for(int upper=0;upper<2;upper++){
  if(upper && (hi>=lo || lo<=single))continue;
  int a=(upper?n+p[hi]:p[lo]),aa=M^a, L=lo+!upper,H=hi+upper;
  int from=0;
  if(k==7){for(int i=1;i<h;i++)from+=both(f[i-1],f[i],M);
   if(h)from+=both(f[h-1],a,M);if(from+best[L][H][upper]<threshold)continue;}
  int undo[130],nundo=0;
  // Record only pairs of already fixed positions, including reflected positions.
  auto record=[&](int early,int late){
    if((early<n)==(late<n))return true;
    bool ordinaryFirst=early<n;
    int ordinary=ordinaryFirst?early:late,shifted=(ordinaryFirst?late:early)-n;
    int key=364+code[ordinary]-code[shifted],orient=ordinaryFirst?1:-1;
    if(sign[key])return sign[key]==orient;
    sign[key]=orient;undo[nundo++]=key;return true;
  };
  bool ok=record(a,aa);
  for(int t=0;t<h&&ok;t++)ok=record(f[t],a)&&record(a,M^f[t]);
  if(ok){f[h]=a;f[M-h]=aa;if(k==7)visits7++;run(L,H);}
  while(nundo)sign[undo[--nundo]]=0;
 }
}
int main(int argc,char**argv){
 threshold=(argc>1?stoi(argv[1]):39);
 int power=1;for(int j=0;j<6;j++){for(int a=0;a<(1<<j);a++)code[(1<<j)|a]=code[a]+power;power*=3;}
 Order p{};p[1]=1;use(p,1);
 for(int k=1;k<=7;k++){int mx=0;for(int i=0;i<128;i++)if(hist[k][i])mx=i;
 cout<<"level "<<k<<" states "<<level[k]<<" max "<<mx<<"\n";}
 cout<<"seven-prefixes "<<visits7<<"\n";
}
