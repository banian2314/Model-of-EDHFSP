/*********************************************
 * OPL 12.9.0.0 Model
 * Author: banian
 * Creation Date: 2024年3月26日 at 下午7:23:14
 *********************************************/
int n = 6;
int m = 3;
int F = 2;
int u1=390;
int u2=300;
//int L11=2;int L12=1;int L13=2;//工厂各阶段机器数量
//int L21=1;int L22=2;int L23=2;
int L10=1;int L11=2;int L12=1;int L13=2;//工厂各阶段机器数量
int L20=1;int L21=1;int L22=2;int L23=2;
int L=2;//每个阶段都有两台机器，且完全相同
range factories = 1..F;
int h = 100000;
range jobs = 1..n;
range stages = 1..m;
//range machines=1..L; //每个阶段都有两台机器，且完全相同
float beta[factories][stages][1..2]=[[[6,8],[7,0],[6,7]],[[7,0],[6,7],[8,9]]];
float gamma=0.7;
float omega=1;
float theta=0.5;
//float P[0..n][1..m] = [[0,0,0],[6,4,6],[4,3.6,5],[6,2.4,3.6],[6,2,3.6]];
float P[0..n][1..m] = [[0,0,0],[6,4,6],[4,3,5],[6,2,3],[6,2,3],[4,7,2],[7,6,5]];
//float P[1..n][1..m] = [[6,4,6],[4,3,5],[6,2,3],[6,2,3],[4,7,2],[7,6,5]];
// 准备时间只与阶段有关(和机器无关)，不管在哪个工厂的哪个阶段只要阶段相同，准备时间便相同
float ST[0..n][0..n][stages] = [[[0,0,0],[1,2,2],[1,3,2],[2,2,3],[2,3,3],[1,2,2],[1,3,2]],
                                 [[0,0,0],[0,0,0],[1,2,2],[1,2,1],[2,2,1],[1,2,2],[1,2,1]],
                                 [[0,0,0],[2,2,1],[0,0,0],[2,1,3],[2,3,4],[3,2,2],[1,2,4]],
                                 [[0,0,0],[2,4,1],[2,3,1],[0,0,0],[2,1,4],[3,2,4],[1,2,4]],
                                 [[0,0,0],[1,3,2],[2,1,5],[2,3,4],[0,0,0],[3,2,2],[4,2,4]],
                                 [[0,0,0],[1,3,2],[2,4,1],[2,3,4],[3,1,2],[0,0,0],[3,2,4]],
                                 [[0,0,0],[2,4,1],[2,3,7],[1,2,4],[2,1,4],[3,2,7],[0,0,0]]];
//float ST[0..n][0..n][stages] = [[[0,0,0],[1,2,2],[1,3,2],[2,2,3],[2,3,3]],
//                                 [[0,0,0],[0,0,0],[1,2,2],[1,2,1],[2,2,1]],
//                                 [[0,0,0],[2,2,1],[0,0,0],[2,1,3],[2,3,4]],
//                                 [[0,0,0],[2,4,1],[2,3,1],[0,0,0],[2,1,4]],
//                                 [[0,0,0],[1,3,2],[2,1,5],[2,3,4],[0,0,0]]];
float v[factories][stages][1..2]=[[[1,1.2],[1.2,0],[1,1.2]],[[1.2,0],[1,1],[1,1.2]]];
//float v[factories][stages][1..2]=[[[1,1],[1,0],[1,1]],[[1,0],[1,1],[1,1]]];
dvar boolean X[0..n][1..F]; 
dvar boolean Y[0..n][1..L][1..F][0..m];
dvar boolean Z[0..n][0..n][1..L][1..F][0..m];
dvar float d[0..n][0..m];
dvar float Cmax;
dvar float TEC;
dvar float PEC[0..n][1..L][1..F][1..m];
dvar float SEC[0..n][1..L][1..F][1..m];
dvar float BEC[0..n][1..L][1..F][1..m];
dvar float IEC[0..n][1..L][1..F][1..m];
minimize Cmax;
//minimize TEC;
//minimize staticLex(TEC,Cmax);
//minimize staticLex(Cmax,TEC);
subject to{
 	// Constraint 2 虚拟工件必须分配在所有工厂中
	forall(f in 1..F) X[0][f] == 1;
	// Constraint 3 任意工件（除虚拟工件）必须分配在其中一个工厂中
   	forall(j in 1..n) sum(f in 1..F) X[j][f] == 1; 
   	// Constraint 4 任意工件（除虚拟工件）必须分配在某一工厂某一阶段的一台机器上
//	forall(j in 1..n,f in 1..F, k in 1..m) sum(i in 1..L) Y[j][i][f][k] == X[j][f];//任意工件只能在不同阶段的其中一个机器上出现 
	forall(j in 1..n) sum(i in 1..L11) Y[j][i][1][1] == X[j][1];
	forall(j in 1..n) sum(i in 1..L12) Y[j][i][1][2] == X[j][1];
	forall(j in 1..n) sum(i in 1..L13) Y[j][i][1][3] == X[j][1];
	forall(j in 1..n) sum(i in 1..L21) Y[j][i][2][1] == X[j][2];
	forall(j in 1..n) sum(i in 1..L22) Y[j][i][2][2] == X[j][2];
	forall(j in 1..n) sum(i in 1..L23) Y[j][i][2][3] == X[j][2];
	//Constraint 5 虚拟工件分配在所有阶段(包括虚拟阶段)的所有机器上
    forall(i in 1..L10) Y[0][i][1][0]==1;
	forall(i in 1..L11) Y[0][i][1][1]==1;
	forall(i in 1..L12) Y[0][i][1][2]==1;
	forall(i in 1..L13) Y[0][i][1][3]==1;
	forall(i in 1..L20) Y[0][i][2][0]==1;
	forall(i in 1..L21) Y[0][i][2][1]==1;
	forall(i in 1..L22) Y[0][i][2][2]==1;
	forall(i in 1..L23) Y[0][i][2][3]==1;
	//只有一个前驱，只有一个后继
	//Constraint 6 如果工件j1不出现在这台机器上，则以j1为前驱的工件绝对没有
//	forall(j1 in 1..n, j2 in 0..n:j1!=j2,i in 1..L,f in 1..F,k in 1..m) Z[j1][j2][i][f][k]<=Y[j1][i][f][k];
	forall(j1 in 1..n, j2 in 0..n:j1!=j2,i in 1..L11) Z[j1][j2][i][1][1]<=Y[j1][i][1][1];
	forall(j1 in 1..n, j2 in 0..n:j1!=j2,i in 1..L12) Z[j1][j2][i][1][2]<=Y[j1][i][1][2];
	forall(j1 in 1..n, j2 in 0..n:j1!=j2,i in 1..L13) Z[j1][j2][i][1][3]<=Y[j1][i][1][3];
	forall(j1 in 1..n, j2 in 0..n:j1!=j2,i in 1..L21) Z[j1][j2][i][2][1]<=Y[j1][i][2][1];
	forall(j1 in 1..n, j2 in 0..n:j1!=j2,i in 1..L22) Z[j1][j2][i][2][2]<=Y[j1][i][2][2];
	forall(j1 in 1..n, j2 in 0..n:j1!=j2,i in 1..L23) Z[j1][j2][i][2][3]<=Y[j1][i][2][3];
	//Constraint 7 如果工件j2不出现在这台机器上，则以j2为后继的工件绝对没有
//	forall(j1 in 0..n, j2 in 1..n:j1!=j2,i in 1..L,f in 1..F,k in 1..m) Z[j1][j2][i][f][k]<=Y[j2][i][f][k];
	forall(j1 in 0..n, j2 in 1..n:j1!=j2,i in 1..L11) Z[j1][j2][i][1][1]<=Y[j2][i][1][1];
	forall(j1 in 0..n, j2 in 1..n:j1!=j2,i in 1..L12) Z[j1][j2][i][1][2]<=Y[j2][i][1][2];
	forall(j1 in 0..n, j2 in 1..n:j1!=j2,i in 1..L13) Z[j1][j2][i][1][3]<=Y[j2][i][1][3];
	forall(j1 in 0..n, j2 in 1..n:j1!=j2,i in 1..L21) Z[j1][j2][i][2][1]<=Y[j2][i][2][1];
	forall(j1 in 0..n, j2 in 1..n:j1!=j2,i in 1..L22) Z[j1][j2][i][2][2]<=Y[j2][i][2][2];
	forall(j1 in 0..n, j2 in 1..n:j1!=j2,i in 1..L23) Z[j1][j2][i][2][3]<=Y[j2][i][2][3];
	// Constraint 8 无子环约束 
    forall(j2 in 0..n, i in 1..L11) sum(j1 in 0..n: j1!=j2) Z[j1][j2][i][1][1] == Y[j2][i][1][1]; 
    forall(j2 in 0..n, i in 1..L12) sum(j1 in 0..n: j1!=j2) Z[j1][j2][i][1][2] == Y[j2][i][1][2];
    forall(j2 in 0..n, i in 1..L13) sum(j1 in 0..n: j1!=j2) Z[j1][j2][i][1][3] == Y[j2][i][1][3];
    forall(j2 in 0..n, i in 1..L21) sum(j1 in 0..n: j1!=j2) Z[j1][j2][i][2][1] == Y[j2][i][2][1]; 
    forall(j2 in 0..n, i in 1..L22) sum(j1 in 0..n: j1!=j2) Z[j1][j2][i][2][2] == Y[j2][i][2][2];
    forall(j2 in 0..n, i in 1..L23) sum(j1 in 0..n: j1!=j2) Z[j1][j2][i][2][3] == Y[j2][i][2][3];
    //Constraint 9 无子环约束 
    forall(j1 in 0..n, i in 1..L11) sum(j2 in 0..n: j1!=j2) Z[j1][j2][i][1][1] == Y[j1][i][1][1];
    forall(j1 in 0..n, i in 1..L12) sum(j2 in 0..n: j1!=j2) Z[j1][j2][i][1][2] == Y[j1][i][1][2];
    forall(j1 in 0..n, i in 1..L13) sum(j2 in 0..n: j1!=j2) Z[j1][j2][i][1][3] == Y[j1][i][1][3];
    forall(j1 in 0..n, i in 1..L21) sum(j2 in 0..n: j1!=j2) Z[j1][j2][i][2][1] == Y[j1][i][2][1];
    forall(j1 in 0..n, i in 1..L22) sum(j2 in 0..n: j1!=j2) Z[j1][j2][i][2][2] == Y[j1][i][2][2];
    forall(j1 in 0..n, i in 1..L23) sum(j2 in 0..n: j1!=j2) Z[j1][j2][i][2][3] == Y[j1][i][2][3];
	//Constraint 10 无子环约束 
    forall(j1 in 1..n,j2 in 1..n:j1!=j2, i in 1..L11) u2-u1+100*Z[j1][j2][i][1][1]<=100-1;
    forall(j1 in 1..n,j2 in 1..n:j1!=j2, i in 1..L12) u2-u1+100*Z[j1][j2][i][1][2]<=100-1;
    forall(j1 in 1..n,j2 in 1..n:j1!=j2, i in 1..L13) u2-u1+100*Z[j1][j2][i][1][3]<=100-1;
    forall(j1 in 1..n,j2 in 1..n:j1!=j2, i in 1..L21) u2-u1+100*Z[j1][j2][i][2][1]<=100-1;
    forall(j1 in 1..n,j2 in 1..n:j1!=j2, i in 1..L22) u2-u1+100*Z[j1][j2][i][2][2]<=100-1;
    forall(j1 in 1..n,j2 in 1..n:j1!=j2, i in 1..L23) u2-u1+100*Z[j1][j2][i][2][3]<=100-1;
    //Constraint 12 虚拟工件在各个机器上的离开时间
        	// Constraint 14 
	forall(j in 0..n,k in 0..m) d[j][k]>=0;
    forall(k in 0..m) d[0][k]==0;
    //Constraint 13 Y[j1][i][1][1]
    forall(j in 1..n, i in 1..L11) d[j][1]>=d[j][0]+P[j][1]/v[1][1][i]+(Y[j][i][1][1]-1)*h;
	forall(j in 1..n, i in 1..L12) d[j][2]>=d[j][1]+P[j][2]/v[1][2][i]+(Y[j][i][1][2]-1)*h;
	forall(j in 1..n, i in 1..L13) d[j][3]>=d[j][2]+P[j][3]/v[1][3][i]+(Y[j][i][1][3]-1)*h;
	forall(j in 1..n, i in 1..L21) d[j][1]>=d[j][0]+P[j][1]/v[2][1][i]+(Y[j][i][2][1]-1)*h;
	forall(j in 1..n, i in 1..L22) d[j][2]>=d[j][1]+P[j][2]/v[2][2][i]+(Y[j][i][2][2]-1)*h;
	forall(j in 1..n, i in 1..L23) d[j][3]>=d[j][2]+P[j][3]/v[2][3][i]+(Y[j][i][2][3]-1)*h;
//	forall(j in 1..n, i in 1..L11) d[j][1]>=d[j][0]+P[j][1]/v[1][1][i]+(X[j][1]-1)*h;
//	forall(j in 1..n, i in 1..L12) d[j][2]>=d[j][1]+P[j][2]/v[1][2][i]+(X[j][1]-1)*h;
//	forall(j in 1..n, i in 1..L13) d[j][3]>=d[j][2]+P[j][3]/v[1][3][i]+(X[j][1]-1)*h;
//	forall(j in 1..n, i in 1..L21) d[j][1]>=d[j][0]+P[j][1]/v[2][1][i]+(X[j][2]-1)*h;
//	forall(j in 1..n, i in 1..L22) d[j][2]>=d[j][1]+P[j][2]/v[2][2][i]+(X[j][2]-1)*h;
//	forall(j in 1..n, i in 1..L23) d[j][3]>=d[j][2]+P[j][3]/v[2][3][i]+(X[j][2]-1)*h;

	// Constraint 15 前提是在当前阶段中，共用同一台机器
	//	forall(j1 in 1..n, j2 in 1..n :j1!=j2,f in 1..F, k in 1..m,i in 1..L) d[j2][k]>=d[j1][k]+P[j2][k]+ST[j1][j2][k]+(Z[j1][j2][i][f][k]-1)*h;
	forall(j1 in 1..n, j2 in 1..n :j1!=j2,i in 1..L11) d[j2][1]>=d[j1][1]+P[j2][1]/v[1][1][i]+ST[j1][j2][1]+(Z[j1][j2][i][1][1]-1)*h;
	forall(j1 in 1..n, j2 in 1..n :j1!=j2,i in 1..L12) d[j2][2]>=d[j1][2]+P[j2][2]/v[1][2][i]+ST[j1][j2][2]+(Z[j1][j2][i][1][2]-1)*h;
	forall(j1 in 1..n, j2 in 1..n :j1!=j2,i in 1..L13) d[j2][3]>=d[j1][3]+P[j2][3]/v[1][3][i]+ST[j1][j2][3]+(Z[j1][j2][i][1][3]-1)*h;
	forall(j1 in 1..n, j2 in 1..n :j1!=j2,i in 1..L21) d[j2][1]>=d[j1][1]+P[j2][1]/v[2][1][i]+ST[j1][j2][1]+(Z[j1][j2][i][2][1]-1)*h;
	forall(j1 in 1..n, j2 in 1..n :j1!=j2,i in 1..L22) d[j2][2]>=d[j1][2]+P[j2][2]/v[2][2][i]+ST[j1][j2][2]+(Z[j1][j2][i][2][2]-1)*h;
	forall(j1 in 1..n, j2 in 1..n :j1!=j2,i in 1..L23) d[j2][3]>=d[j1][3]+P[j2][3]/v[2][3][i]+ST[j1][j2][3]+(Z[j1][j2][i][2][3]-1)*h;
       	    //Constraint 11 工件在不同阶段的完工时间约束
	//forall(j in 1..n, k in 1..m,f in 1..F) d[j][k]>=d[j][k-1]+P[j][k]+(X[j][f]-1)*h;
	forall(j1 in 0..n, j2 in 1..n :j1!=j2, i in 1..L11) d[j2][0]>=d[j1][1]+ST[j1][j2][1]+(Z[j1][j2][i][1][1]-1)*h;
	forall(j1 in 0..n, j2 in 1..n :j1!=j2, i in 1..L12) d[j2][1]>=d[j1][2]+ST[j1][j2][2]+(Z[j1][j2][i][1][2]-1)*h;
	forall(j1 in 0..n, j2 in 1..n :j1!=j2, i in 1..L13) d[j2][2]>=d[j1][3]+ST[j1][j2][3]+(Z[j1][j2][i][1][3]-1)*h;
	forall(j1 in 0..n, j2 in 1..n :j1!=j2, i in 1..L21) d[j2][0]>=d[j1][1]+ST[j1][j2][1]+(Z[j1][j2][i][2][1]-1)*h;
	forall(j1 in 0..n, j2 in 1..n :j1!=j2, i in 1..L22) d[j2][1]>=d[j1][2]+ST[j1][j2][2]+(Z[j1][j2][i][2][2]-1)*h;
	forall(j1 in 0..n, j2 in 1..n :j1!=j2, i in 1..L23) d[j2][2]>=d[j1][3]+ST[j1][j2][3]+(Z[j1][j2][i][2][3]-1)*h;
	   	// Constraint 16
	//工件在最后一个阶段的完工时间=该工件在前一个阶段的完工时间+该工件在最后阶段的加工时间
	//forall(j in 1..n,f in 1..F) d[j][m]<=d[j][m-1]+P[j][m]-(X[j][f]-1)*h;
	forall(j in 0..n,i in 1..L13) d[j][m]<=d[j][m-1]+P[j][m]/v[1][m][i]-(Y[j][i][1][m]-1)*h;
	forall(j in 0..n,i in 1..L23) d[j][m]<=d[j][m-1]+P[j][m]/v[2][m][i]-(Y[j][i][2][m]-1)*h;
	// Constraint 17 前提是当前工件位于首位置
//	forall(j in 1..n, f in 1..F,k in 1..m,i in 1..L) d[j][k]>=P[j][k]+STS[j][k]+(Z[0][j][i][f][k]-1)*h;
	forall(j in 1..n, i in 1..L11) d[j][1]>=P[j][1]/v[1][1][i]+ST[0][j][1]+(Z[0][j][i][1][1]-1)*h;
	forall(j in 1..n, i in 1..L12) d[j][2]>=P[j][2]/v[1][2][i]+ST[0][j][2]+(Z[0][j][i][1][2]-1)*h;
	forall(j in 1..n, i in 1..L13) d[j][3]>=P[j][3]/v[1][3][i]+ST[0][j][3]+(Z[0][j][i][1][3]-1)*h;
	forall(j in 1..n, i in 1..L21) d[j][1]>=P[j][1]/v[2][1][i]+ST[0][j][1]+(Z[0][j][i][2][1]-1)*h;
	forall(j in 1..n, i in 1..L22) d[j][2]>=P[j][2]/v[2][2][i]+ST[0][j][2]+(Z[0][j][i][2][2]-1)*h;
	forall(j in 1..n, i in 1..L23) d[j][3]>=P[j][3]/v[2][2][i]+ST[0][j][3]+(Z[0][j][i][2][3]-1)*h;
	  // Constraint 
    forall(j in 0..n,i in 1..L,f in 1..F,k in 1..m) PEC[j][i][f][k]>=0;
    forall(j in 0..n,i in 1..L,f in 1..F,k in 1..m) SEC[j][i][f][k]>=0;
    forall(j in 0..n,i in 1..L,f in 1..F,k in 1..m) BEC[j][i][f][k]>=0;
    forall(j in 0..n,i in 1..L,f in 1..F,k in 1..m) IEC[j][i][f][k]>=0;
      // Constraint 18
	forall(j in 1..n,i in 1..L11) PEC[j][i][1][1]>=beta[1][1][i]*P[j][1]/v[1][1][i]+(Y[j][i][1][1]-1)*h;
	forall(j in 1..n,i in 1..L12) PEC[j][i][1][2]>=beta[1][2][i]*P[j][2]/v[1][2][i]+(Y[j][i][1][2]-1)*h;
	forall(j in 1..n,i in 1..L13) PEC[j][i][1][3]>=beta[1][3][i]*P[j][3]/v[1][3][i]+(Y[j][i][1][3]-1)*h;
	forall(j in 1..n,i in 1..L21) PEC[j][i][2][1]>=beta[2][1][i]*P[j][1]/v[2][1][i]+(Y[j][i][2][1]-1)*h;
	forall(j in 1..n,i in 1..L22) PEC[j][i][2][2]>=beta[2][2][i]*P[j][2]/v[2][2][i]+(Y[j][i][2][2]-1)*h;
	forall(j in 1..n,i in 1..L23) PEC[j][i][2][3]>=beta[2][3][i]*P[j][3]/v[2][3][i]+(Y[j][i][2][3]-1)*h;
     // Constraint 19
	forall(j1 in 0..n,j2 in 1..n:j1!=j2,i in 1..L11) SEC[j2][i][1][1]>=gamma*ST[j1][j2][1]+(Z[j1][j2][i][1][1]-1)*h;
	forall(j1 in 0..n,j2 in 1..n:j1!=j2,i in 1..L12) SEC[j2][i][1][2]>=gamma*ST[j1][j2][2]+(Z[j1][j2][i][1][2]-1)*h;
	forall(j1 in 0..n,j2 in 1..n:j1!=j2,i in 1..L13) SEC[j2][i][1][3]>=gamma*ST[j1][j2][3]+(Z[j1][j2][i][1][3]-1)*h;
	forall(j1 in 0..n,j2 in 1..n:j1!=j2,i in 1..L11) SEC[j2][i][2][1]>=gamma*ST[j1][j2][1]+(Z[j1][j2][i][2][1]-1)*h;
	forall(j1 in 0..n,j2 in 1..n:j1!=j2,i in 1..L12) SEC[j2][i][2][2]>=gamma*ST[j1][j2][2]+(Z[j1][j2][i][2][2]-1)*h;
	forall(j1 in 0..n,j2 in 1..n:j1!=j2,i in 1..L13) SEC[j2][i][2][3]>=gamma*ST[j1][j2][3]+(Z[j1][j2][i][2][3]-1)*h;
    // Constraint 20
    forall(j in 0..n,i in 1..L11) BEC[j][i][1][1]>=omega*(d[j][1]-d[j][0]-P[j][1]/v[1][1][i])+(Y[j][i][1][1]-1)*h;  
    forall(j in 0..n,i in 1..L12) BEC[j][i][1][2]>=omega*(d[j][2]-d[j][1]-P[j][2]/v[1][2][i])+(Y[j][i][1][2]-1)*h;
    forall(j in 0..n,i in 1..L13) BEC[j][i][1][3]>=omega*(d[j][3]-d[j][2]-P[j][3]/v[1][3][i])+(Y[j][i][1][3]-1)*h;
    forall(j in 0..n,i in 1..L21) BEC[j][i][2][1]>=omega*(d[j][1]-d[j][0]-P[j][1]/v[2][1][i])+(Y[j][i][2][1]-1)*h;  
    forall(j in 0..n,i in 1..L22) BEC[j][i][2][2]>=omega*(d[j][2]-d[j][1]-P[j][2]/v[2][2][i])+(Y[j][i][2][2]-1)*h;
    forall(j in 0..n,i in 1..L23) BEC[j][i][2][3]>=omega*(d[j][3]-d[j][2]-P[j][3]/v[2][3][i])+(Y[j][i][2][3]-1)*h;
    // Constraint 21
    forall(j1 in 0..n,j2 in 1..n:j1!=j2,i in 1..L11) IEC[j1][i][1][1]>=theta*(d[j2][0]-d[j1][1]-ST[j1][j2][1])+(Z[j1][j2][i][1][1]-1)*h; 
    forall(j1 in 0..n,j2 in 1..n:j1!=j2,i in 1..L12) IEC[j1][i][1][2]>=theta*(d[j2][1]-d[j1][2]-ST[j1][j2][2])+(Z[j1][j2][i][1][2]-1)*h;
	forall(j1 in 0..n,j2 in 1..n:j1!=j2,i in 1..L13) IEC[j1][i][1][3]>=theta*(d[j2][2]-d[j1][3]-ST[j1][j2][3])+(Z[j1][j2][i][1][3]-1)*h;
    forall(j1 in 0..n,j2 in 1..n:j1!=j2,i in 1..L21) IEC[j1][i][2][1]>=theta*(d[j2][0]-d[j1][1]-ST[j1][j2][1])+(Z[j1][j2][i][2][1]-1)*h; 
    forall(j1 in 0..n,j2 in 1..n:j1!=j2,i in 1..L22) IEC[j1][i][2][2]>=theta*(d[j2][1]-d[j1][2]-ST[j1][j2][2])+(Z[j1][j2][i][2][2]-1)*h;
	forall(j1 in 0..n,j2 in 1..n:j1!=j2,i in 1..L23) IEC[j1][i][2][3]>=theta*(d[j2][2]-d[j1][3]-ST[j1][j2][3])+(Z[j1][j2][i][2][3]-1)*h;	
    // Constraint 22
    TEC>=sum(f in 1..F,k in 1..m,i in 1..L,j in 0..n) (PEC[j][i][f][k]+SEC[j][i][f][k]+BEC[j][i][f][k]+IEC[j][i][f][k]);
	TEC<=544;
	// Constraint 23
	forall(j in 1..n) Cmax >= d[j][m];
	//Cmax<=21;
}