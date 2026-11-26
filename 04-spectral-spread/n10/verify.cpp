#include <array>
#include <gmpxx.h>
#include <cstdint>
#include <cstdlib>
#include <fstream>
#include <iostream>
#include <stdexcept>
#include <string>
#include <vector>
using cpp_int=mpz_class;
using namespace std;
constexpr int n=10, mask_count=1<<(2*n-1);
constexpr long scale=1000000;
using Hmat=array<array<int,n>,n>;
using Zmat=array<array<cpp_int,n>,n>;

bool spd(Zmat M,int r) {
 cpp_int old=1;
 for(int k=0;k<r;k++){
  const cpp_int p=M[k][k];
  if(p<=0)return false;
  if(k+1==r)return true;
  for(int i=k+1;i<r;i++)for(int j=i;j<r;j++)
   M[i][j]=(p*M[i][j]-M[k][i]*M[k][j])/old;
  old=p;
 }
 throw runtime_error("invalid dimension");
}
Hmat form(int mask){
 Hmat h{};
 for(int i=0;i<n;i++)for(int j=0;j<n;j++) {
  const int bit_i=i ? ((mask>>(i-1))&1):0;
  const int bit_j=j ? ((mask>>(j-1))&1):0;
  h[i][j]=bit_i^bit_j^((mask>>(n-1+min(i,j)))&1);
 }
 return h;
}
int classify(const Hmat &h){
 array<int,n> v{},w{},z{};
 int k=0,first=-1;
 for(int i=0;i<n;i++){v[i]=h[i][i]; k+=v[i]; if(v[i]&&first<0)first=i;}
 bool canonical=true;
 for(int i=0;i<n;i++)for(int j=0;j<n;j++)canonical&=h[i][j]==v[i]*v[j];
 if(canonical)return 1;
 if(first<0)return 0;
 int k1=0,k2=0;
 for(int i=0;i<n;i++){
  w[i]=h[first][i];
  if(w[i]>v[i])return 0;
  z[i]=v[i]-w[i]; k1+=w[i]; k2+=z[i];
 }
 if(!k1||!k2||((k1!=k2)&&!(k1*k2==6&&k1+k2==5)))return 0;
 for(int i=0;i<n;i++)for(int j=0;j<n;j++)if(h[i][j]!=w[i]*w[j]+z[i]*z[j])return 0;
 return k1==k2 ? 2 : 3;
}
struct Reduced { int r=0; array<int,n> rep{}, mult{}; Hmat h{}; };
Reduced reduce(const Hmat &h){
 Reduced s;
 for(int i=0;i<n;i++) {
  int j=0; while(j<s.r && h[i]!=h[s.rep[j]])j++;
  if(j==s.r) {s.rep[s.r]=i;s.r++;}
  s.mult[j]++;
 }
 for(int i=0;i<s.r;i++)for(int j=0;j<s.r;j++)s.h[i][j]=h[s.rep[i]][s.rep[j]];
 return s;
}
bool pd_shift(const Reduced &s,int64_t a,int64_t q,int64_t x,int sign){
 if(s.r<n&&sign*x>=0)return false; // sign(A-xI) restricted to the exact zero eigenspace.
 Zmat mat{};
 for(int i=0;i<s.r;i++)for(int j=i;j<s.r;j++){
  cpp_int v=(q-(q-a)*s.h[i][j])*scale*s.mult[j];
  if(i==j)v-=cpp_int(x)*q;
  mat[i][j]=sign*v*s.mult[i];
 }
 return spd(std::move(mat),s.r);
}
bool near_one(const Hmat &h){
 int rowtotal=0;
 for(auto &row:h)for(int x:row)rowtotal+=x;
 Zmat mat{};
 for(int i=0;i<n-1;i++)for(int j=i;j<n-1;j++) {
   int e=h[i][j]-h[n-1][j]-h[i][n-1]+h[n-1][n-1];
   mat[i][j]=(1000*rowtotal+1171*n)*(1+(i==j))-1000*n*e;
 }
 return spd(std::move(mat),n-1);
}
int64_t read32(ifstream &f) {
 array<unsigned char,4> b{};
 if(!f.read(reinterpret_cast<char*>(b.data()),4))throw runtime_error("truncated lower file");
 uint32_t d=uint32_t(b[0])+(uint32_t(b[1])<<8)+(uint32_t(b[2])<<16)+(uint32_t(b[3])<<24);
 return d>= (uint32_t(1)<<31) ? int64_t(d)-(int64_t(1)<<32):int64_t(d);
}
int main(int argc,char**argv){
 if(argc==2&&string(argv[1])=="left"){
  ifstream file("left.bin",ios::binary);
  int checks=0;
  for(int mask=0;mask<(1<<n);mask++){
   int changes=0;
   for(int i=0;i<n-1;i++)changes+=((mask>>i)^(mask>>(i+1)))&1;
   if(changes<2)continue; // rank-one and rank-two sign forms treated analytically
   int64_t L=read32(file);
   const auto pattern=reduce(form(mask<<(n-1)));
   if(!pd_shift(pattern,-1,1,L,1)||!pd_shift(pattern,-1,1,L+14140000,-1))
     throw runtime_error("left endpoint failed at eps mask "+to_string(mask));
   checks+=2;
  }
  if(file.peek()!=EOF)throw runtime_error("extra lower values");
  cout<<"left endpoint: "<<checks<<" exact PD tests passed; remaining forms have at most two sign runs\n";
  return 0;
 }
 vector<Reduced> patterns;
 vector<int> ids;
 int canonical=0,clusters=0,mixed=0;
 for(int mask=0;mask<mask_count;mask++){
  const Hmat h=form(mask);
  const int ex=classify(h);
  if(ex==1){canonical++;continue;}
  if(ex==2){clusters++;continue;}
  if(ex==3){mixed++;continue;}
  if(argc==1&&!near_one(h))throw runtime_error("near-one failed at mask "+to_string(mask));
  patterns.push_back(reduce(h)); ids.push_back(mask);
 }
 if(argc==1){
  cout<<"near-one certified for "<<patterns.size()<<" patterns; "<<canonical<<" canonical and "<<clusters<<" equal two-cluster and "<<mixed<<" mixed two-cluster patterns proved analytically\n";
  return 0;
 }
 ifstream pts("points.tsv");
 int64_t a,q,U; int index=0, seen=0;
 const int from=stoi(argv[1]), to=argc==3?stoi(argv[2]):from+1;
 while(pts>>a>>q>>U){
  int j=index++;
  if(j<from||j>=to)continue;
  if(q<=0||q>1000000||a< -q||a>=q||U<=0||U>20000000)throw runtime_error("malformed certificate point");
  string k=to_string(j); k=string(3-k.size(),'0')+k;
  ifstream file("lower"+k+".bin",ios::binary);
  for(size_t i=0;i<patterns.size();i++){
   int64_t L=read32(file);
   if(!pd_shift(patterns[i],a,q,L,1)||!pd_shift(patterns[i],a,q,L+U,-1))
    throw runtime_error("failed node "+to_string(j)+" mask "+to_string(ids[i]));
  }
  if(file.peek()!=EOF)throw runtime_error("extra lower values");
  cout<<"node "<<j<<" a="<<a<<"/"<<q<<" U="<<U<<"/"<<scale<<": "<<2*patterns.size()<<" exact PD tests passed"<<endl;
  seen++;
 }
 if(seen!=to-from)throw runtime_error("node range not fully covered");
}
