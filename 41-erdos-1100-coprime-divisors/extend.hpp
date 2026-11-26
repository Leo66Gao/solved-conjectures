// For a fixed order at six atoms, rule out lexicographically coherent extensions
// whose disjoint-neighbor count reaches TARGET, or output one.
constexpr int N=64, MASK=127; int TARGET=39; long long nodes=0, leaves=0, bases=0;
int ub[N+1][N+1][2], idd[N][N],pc[N],tx[2*N],history[N*N];
unsigned char sg[N*N]; int top;
int gain(int a,int b){return (!(a&b))+((a|b)==MASK);}
int setsg(int d,int v){if(sg[d])return sg[d]==v;sg[d]=v;history[top++]=d;return 1;}
bool dfs7(const string&s,int x,int y,int z,int score){
 int t=x+y; if(score+ub[x][y][z]<TARGET)return false;
 nodes++;
 if(t==N){
   leaves++;int total=score+1;
   if(leaves<=10){cout<<"candidate "<<total<<" :"; for(int i=0;i<N;i++)cout<<" "<<tx[i];cout<<'\n';}
   return true;
 }
 int prev=tx[t-1]; bool found=false;
 for(int l=0;l<2;l++){
  if((!l && x>=N)||(l && (y>=x || x<=pc[32])))continue;
  int v=l?(s[y]+N):s[x],xx=x+!l,yy=y+l,ss=score+gain(prev,v);
  if(ss+ub[xx][yy][l]<TARGET)continue;
  // Append v, forcing its comparison against every remaining element of the other layer.
  int checkpoint=top,j;bool ok=true;
  if(!l){for(j=y;j<N;j++)if(!setsg(idd[x][j],1)){ok=false;break;}}
  else {for(j=x;j<N;j++)if(!setsg(idd[j][y],2)){ok=false;break;}}
  if(ok){tx[t]=v;found|=dfs7(s,xx,yy,l,ss);}
  while(top>checkpoint)sg[history[--top]]=0;
 }
 return found;
}
void test7(const string &s){
 for(int i=0;i<N;i++)pc[int(s[i])]=i;
 // Compute best possible suffix score in an arbitrary merge, without translation constraints.
 for(int t=N;t>=1;t--)for(int x=(t+1)/2;x<=t;x++){
   int y=t-x;for(int z=0;z<2;z++){int h=-1000;
    if((!z&&x)||(z&&y)){
      if(t==N)h=1;
      else{
        int prev=z?(N+s[y-1]):s[x-1];
        if(x<N)h=gain(prev,s[x])+ub[x+1][y][0];
        if(y<x&&x>pc[32])h=max(h,gain(prev,s[y]+N)+ub[x][y+1][1]);
      }
    }ub[x][y][z]=h;
   }
 }
 if(ub[1][0][0]<TARGET)return; bases++;
 // Register relations which follow from w7>w6, and coordinate comparisons.
 fill(sg,sg+N*N,0);top=0;
 for(int x=0;x<N;x++)for(int y=0;y<N;y++){
  int j=s[x],i=s[y],a=j&~i,b=i&~j, d=a*N+b; idd[x][y]=d;
  if(pc[a]<=pc[b] || (!(b&32) && pc[a]<=pc[b|32]) || ((a&32) && pc[a^32]<=pc[b])) sg[d]=1;
 }
 tx[0]=0; dfs7(s,1,0,0,0);
}
