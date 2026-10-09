/* MIT License, Copyright (c) 2026 GPT.
 * A small C bot: tactical play, alpha-beta search, and a preserved 7-column,
 * 6-row first-player winning policy. Compile natively or to WebAssembly.
 * Browser rendering and asynchronous worker control are separate JavaScript.
 */
typedef unsigned char u8;
typedef unsigned int u32;
typedef unsigned long long u64;

#ifdef __wasm__
__attribute__((import_module("env"),import_name("now"))) extern double bot_now(void);
#else
#include <stdio.h>
#include <stdlib.h>
#include <time.h>
static double bot_now(void) { return 1000.0 * (double)clock() / CLOCKS_PER_SEC; }
#endif

#define LIMIT 20
#define CELLS 400
#define MATE 1000000
#define INF 2000000
#define TT_SIZE (1u << 18)
#define POLICY_CAPACITY 60000000u

static u8 history[CELLS], board[CELLS], heights[LIMIT];
static u8 policy[POLICY_CAPACITY];
static int rows,cols,stones,standard,window_count;
static unsigned short windows[1400][4];
static u64 black_bits,occupied,bottom_mask,board_mask,hash,zobrist[2][CELLS];
static double deadline;
static int stopped,stat_depth,stat_source,stat_score;
static u32 nodes,generation=1;
typedef struct { u64 key; int score; unsigned short depth; u8 flag,move; u32 age; } Entry;
static Entry tt[TT_SIZE];

static u32 le32(const u8 *p) { return (u32)p[0] | ((u32)p[1]<<8) | ((u32)p[2]<<16) | ((u32)p[3]<<24); }
static int absolute(int x) { return x<0?-x:x; }
static u64 mix(u64 x) { x^=x>>30;x*=0xbf58476d1ce4e5b9ULL;x^=x>>27;x*=0x94d049bb133111ebULL;return x^(x>>31); }
static int count_bits(u64 x) { return __builtin_popcountll(x); }
static int four(u64 x) {
  const int shifts[4]={1,7,6,8};
  for(int i=0;i<4;i++) { u64 p=x&(x>>shifts[i]);if(p&(p>>(2*shifts[i])))return 1; }
  return 0;
}
static u64 winning_squares(u64 p,u64 mask) {
  const int shifts[4]={1,7,6,8};u64 w=0;
  for(int i=0;i<4;i++) { int d=shifts[i];
    w|=(p>>d)&(p>>(2*d))&(p>>(3*d));
    w|=(p<<d)&(p>>d)&(p>>(2*d));
    w|=(p<<(2*d))&(p<<d)&(p>>d);
    w|=(p<<(3*d))&(p<<(2*d))&(p<<d);
  }
  return w&board_mask&~mask;
}
static void place(int c,int player) {
  int r=heights[c]++;board[r*cols+c]=(u8)player;stones++;
  hash^=zobrist[player-1][r*cols+c];
  if(standard) { u64 bit=1ULL<<(7*c+r);occupied|=bit;if(player==1)black_bits|=bit; }
}
static void unplace(int c,int player) {
  int r=--heights[c];board[r*cols+c]=0;stones--;
  hash^=zobrist[player-1][r*cols+c];
  if(standard) { u64 bit=1ULL<<(7*c+r);occupied^=bit;if(player==1)black_bits^=bit; }
}
static int won(int c,int player) {
  if(standard)return four(player==1?black_bits:occupied^black_bits);
  const int dx[4]={1,0,1,1},dy[4]={0,1,1,-1};int row=heights[c]-1;
  for(int d=0;d<4;d++) {
    int n=1;
    for(int sign=-1;sign<=1;sign+=2) {
      int x=c+sign*dx[d],y=row+sign*dy[d];
      while(x>=0&&x<cols&&y>=0&&y<rows&&board[y*cols+x]==player) { n++;x+=sign*dx[d];y+=sign*dy[d]; }
    }
    if(n>=4)return 1;
  }
  return 0;
}
static int immediate_mask(int player) {
  int result=0;
  if(standard) {
    u64 p=player==1?black_bits:occupied^black_bits;
    u64 win=winning_squares(p,occupied)&((occupied+bottom_mask)&board_mask);
    for(int c=0;c<7;c++)if(win&(63ULL<<(7*c)))result|=1<<c;
    return result;
  }
  for(int c=0;c<cols;c++)if(heights[c]<rows) { place(c,player);if(won(c,player))result|=1<<c;unplace(c,player); }
  return result;
}
static int evaluate(int player) {
  const int weight[5]={0,2,13,85,5000};int result=0;
  for(int i=0;i<window_count;i++) {
    int own=0,enemy=0;
    for(int j=0;j<4;j++) { int p=board[windows[i][j]];own+=p==player;enemy+=p!=0&&p!=player; }
    if(!enemy)result+=weight[own];if(!own)result-=weight[enemy];
  }
  for(int r=0;r<rows;r++)for(int c=0;c<cols;c++) {
    int p=board[r*cols+c],center=cols-absolute(2*c-(cols-1));
    if(p)result+=(p==player?1:-1)*center;
  }
  return result;
}
static int easy_move(int player) {
  int best=-1,value=-INF;
  for(int c=0;c<cols;c++)if(heights[c]<rows) {
    place(c,player);int score=cols-absolute(2*c-(cols-1));
    // Easy develops its own shapes without adversarial lookahead or automatic
    // threat blocking. It still takes an immediate win when one is available.
    for(int i=0;i<window_count;i++) {
      int own=0,enemy=0;
      for(int k=0;k<4;k++) { int p=board[windows[i][k]];own+=p==player;enemy+=p!=0&&p!=player; }
      if(!enemy)score+=own*own;
    }
    unplace(c,player);if(score>value) { value=score;best=c; }
  }
  stat_depth=1;stat_score=value;return best;
}
static int order(int player,int preferred,int *moves) {
  int n=0,score[LIMIT],enemy=immediate_mask(3-player);
  u64 safe=0;
  if(standard) {
    u64 possible=(occupied+bottom_mask)&board_mask;
    u64 opp=winning_squares(player==1?occupied^black_bits:black_bits,occupied);
    u64 forced=possible&opp;
    if(forced&&(forced&(forced-1)))return 0;
    if(forced)possible=forced;
    safe=possible&~(opp>>1);
  }
  for(int c=0;c<cols;c++)if(heights[c]<rows) {
    if(standard&&!(safe&(1ULL<<(7*c+heights[c]))))continue;
    if(!standard&&enemy&&(enemy&(enemy-1))==0&&!(enemy&(1<<c)))continue;
    int s=-absolute(2*c-(cols-1))*3+(c==preferred?100000:0);
    if(standard) {
      u64 bit=1ULL<<(7*c+heights[c]),p=player==1?black_bits:occupied^black_bits;
      s+=count_bits(winning_squares(p|bit,occupied|bit))*16;
    }
    int at=n++;
    while(at>0&&score[at-1]<s) { score[at]=score[at-1];moves[at]=moves[at-1];at--; }
    score[at]=s;moves[at]=c;
  }
  return n;
}
static int search(int player,int depth,int alpha,int beta,int ply) {
  nodes++;
  if((nodes&511u)==0&&bot_now()>=deadline)stopped=1;
  if(stopped)return 0;
  if(stones==rows*cols)return 0;
  if(immediate_mask(player))return MATE-ply-1;
  int threats=immediate_mask(3-player);
  if(threats&&(threats&(threats-1)))return -MATE+ply+2;
  if(depth<=0&&!threats)return evaluate(player);
  // Extend a forced block at the horizon, at most four half-moves.
  if(depth<=-4)return evaluate(player);
  u64 key=standard?(occupied+(player==1?black_bits:occupied^black_bits)):hash^mix((u64)player+400);
  Entry *entry=&tt[(u32)mix(key)&(TT_SIZE-1)];
  int original_alpha=alpha,original_beta=beta,preferred=-1;
  if(entry->age==generation&&entry->key==key) {
    preferred=entry->move;
    if(depth>0&&entry->depth>=(unsigned)depth) {
      if(entry->flag==0)return entry->score;
      if(entry->flag==1&&entry->score>=beta)return entry->score;
      if(entry->flag==2&&entry->score<=alpha)return entry->score;
    }
  }
  int moves[LIMIT],n=order(player,preferred,moves),best=-INF,best_move=0;
  if(!n)return -MATE+ply+2;
  for(int i=0;i<n;i++) {
    int c=moves[i];place(c,player);
    int score=won(c,player)?MATE-ply-1:-search(3-player,depth-1,-beta,-alpha,ply+1);
    unplace(c,player);
    if(stopped)return 0;
    if(score>best) { best=score;best_move=c; }
    if(score>alpha)alpha=score;if(alpha>=beta)break;
  }
  if(depth>0) {
    entry->key=key;entry->age=generation;entry->depth=(unsigned short)depth;
    entry->score=best;entry->move=(u8)best_move;
    entry->flag=(u8)(best<=original_alpha?2:best>=original_beta?1:0);
  }
  return best;
}
static int certified_move(int count,u32 size) {
  if(!count)return 3;
  if(count<2||(count&1)||history[0]!=3||size<40)return -1;
  if(policy[0]!='N'||policy[1]!='C'||policy[2]!='4'||policy[3]!='P'||policy[4]!='O'||policy[5]!='L'||policy[6]!='1')return -1;
  u32 total=le32(policy+8);if(total>3000000u||40u+total*4u>size)return -1;
  int first=history[1],mirror=first>3,root=mirror?6-first:first;
  mirror^=(le32(policy+32)>>root)&1u;
  u32 node=le32(policy+16+root*4);
  for(int k=2;;k+=2) {
    if(node>=total)return -1;
    u32 offset=le32(policy+40+node*4);if(offset+2u>size)return -1;
    int column=policy[offset],flags=policy[offset+1];if(column>6)return -1;
    int actual=mirror?6-column:column;
    if(k==count)return heights[actual]<rows?actual:-1;
    if(history[k]!=actual||!(flags&1)||offset+30u>size)return -1;
    int reply=mirror?6-history[k+1]:history[k+1];
    node=le32(policy+offset+2+reply*4);
    mirror^=(flags>>(reply+1))&1;
  }
}

u32 bot_history_pointer(void) { return (u32)(unsigned long long)history; }
u32 bot_policy_pointer(void) { return (u32)(unsigned long long)policy; }
int bot_depth(void) { return stat_depth; }
int bot_source(void) { return stat_source; }
int bot_score(void) { return stat_score; }
u32 bot_nodes(void) { return nodes; }
int bot_choose(int height,int width,int difficulty,int count,u32 policy_size) {
  if(height<1||height>20||width<1||width>20||count<0||count>height*width||difficulty<1||difficulty>3||policy_size>POLICY_CAPACITY)return -1;
  rows=height;cols=width;stones=0;standard=rows==6&&cols==7;
  black_bits=occupied=bottom_mask=board_mask=hash=0;window_count=0;
  for(int i=0;i<CELLS;i++) { board[i]=0;zobrist[0][i]=mix(i+1000);zobrist[1][i]=mix(i+2000); }
  for(int c=0;c<cols;c++)heights[c]=0;
  if(standard)for(int c=0;c<7;c++) { bottom_mask|=1ULL<<(7*c);board_mask|=63ULL<<(7*c); }
  for(int i=0;i<count;i++) {
    int c=history[i];if(c>=cols||heights[c]>=rows)return -1;
    int player=1+(i&1);place(c,player);
    if(won(c,player))return i==count-1?-2:-1;
  }
  if(count==height*width)return -2;
  const int dx[4]={1,0,1,1},dy[4]={0,1,1,-1};
  for(int r=0;r<rows;r++)for(int c=0;c<cols;c++)for(int d=0;d<4;d++) {
    int end_c=c+3*dx[d],end_r=r+3*dy[d];
    if(end_c<0||end_c>=cols||end_r<0||end_r>=rows)continue;
    for(int k=0;k<4;k++)windows[window_count][k]=(unsigned short)((r+k*dy[d])*cols+c+k*dx[d]);
    window_count++;
  }
  int player=1+(count&1);stat_depth=0;stat_source=0;stat_score=0;nodes=0;stopped=0;generation++;
  if(difficulty==3&&standard&&player==1) {
    int move=certified_move(count,policy_size);
    if(move>=0) { stat_source=2;return move; }
  }
  int wins=immediate_mask(player);
  if(wins) { for(int c=0;c<cols;c++)if(wins&(1<<c)) { stat_score=MATE-1;stat_source=1;return c; } }
  if(difficulty==1)return easy_move(player);
  int candidates[LIMIT],n=order(player,-1,candidates);
  if(!n)for(int c=0;c<cols;c++)if(heights[c]<rows)candidates[n++]=c;
  int best=candidates[0];
  const int max_depth[3]={1,4,24},budget[3]={1,150,1800};
  deadline=bot_now()+budget[difficulty-1];
  if(standard&&count==0)best=3;
  for(int depth=1;depth<=max_depth[difficulty-1]&&depth<=rows*cols-count;depth++) {
    int this_best=best,value=-INF,alpha=-INF;
    n=order(player,best,candidates);if(!n)break;
    for(int i=0;i<n;i++) {
      int c=candidates[i];place(c,player);
      int score=won(c,player)?MATE-1:-search(3-player,depth-1,-INF,-alpha,1);
      unplace(c,player);
      if(stopped)break;
      if(score>value) { value=score;this_best=c; }
      if(score>alpha)alpha=score;
    }
    if(stopped)break;
    best=this_best;stat_score=value;stat_depth=depth;
    if(absolute(value)>MATE-500||depth==rows*cols-count||bot_now()>=deadline)break;
  }
  return best;
}

#ifndef __wasm__
int main(int argc,char **argv) {
  if(argc<4) { fprintf(stderr,"Usage: bot ROWS COLUMNS LEVEL [comma-separated 1-based moves] [policy-file]\n");return 2; }
  int count=0;
  if(argc>=5) {
    char *p=argv[4];while(*p) { char *end;long c=strtol(p,&end,10);if(p==end||c<1||c>20||count>=400)return 2;history[count++]=(u8)(c-1);p=end;if(*p==',')p++;else if(*p)return 2; }
  }
  u32 size=0;
  if(argc>=6) { FILE *f=fopen(argv[5],"rb");if(!f)return 2;size=(u32)fread(policy,1,POLICY_CAPACITY,f);fclose(f); }
  int move=bot_choose(atoi(argv[1]),atoi(argv[2]),atoi(argv[3]),count,size);
  printf("{\"column\":%d,\"depth\":%d,\"nodes\":%u,\"source\":%d,\"score\":%d}\n",move>=0?move+1:move,stat_depth,nodes,stat_source,stat_score);
  return move>=0?0:1;
}
#endif
