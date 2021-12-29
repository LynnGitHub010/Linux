#include<iostream>
using namespace std;
#include<stdio.h>
#include<limits.h>
#include<stdlib.h>
#define UNVISITED 0
#define VISITED 1
#define INFINITY INT_MAX
#define ERROR -1
#define OK 1
#define OVERFLOW 0
#define UNSELECTED 0
#define SELECTED 1

typedef int Status;
typedef enum{DG,DN,UDG,UDN} GraphKind;   //图的四种类型：有向图，有向带权图，无向图和无向带权图

typedef struct{
    int symbol;//位置代号
    char *name;//位置名字
    char *introduction;//位置简介
}spot;          //位置类型
 
typedef struct{
    spot v,w;   //边的端点
    int info;   //对带权图，为权值，此处为距离
}ArcInfo;   //存储边信息
 
typedef struct{
    spot *vexs;  //顶点数组，spot是位置类型
    int **arcs;  //关系数组，此图为带权图，则为权值或INFINITY
    int n,e;     //顶点数和边数
    GraphKind kind;//   图的类型
    int *tags;   //标志数组，可用于在图的遍历中标记顶点访问与否
}MGraph;    
 
typedef struct{
    int prev;   //当前最短路径上该顶点的前驱顶点的位序
    int lowcost;//当前最短路径的长度
}DistInfo;
 
 //根据顶点本身数据，判断出顶点在二维数组中的位置
Status LocateVex(MGraph G,spot v){
    int i;
    for(i=0;i<G.n;i++)
        if(v.symbol==G.vexs[i].symbol) return i;
    return ERROR;
}
 //初始化含n个顶点且无边的kind类的图G
Status InitGraph(MGraph &G,spot *vexs,int n){
    int i,j,info;
    if(n<0||(n>0&&NULL==vexs)) return ERROR;
    if(G.kind!=UDN) return ERROR;
    info=INFINITY;  //带权图
    G.n = n;
    G.e = 0;  //顶点数和边数
    if(0==G.n) return OK;   //空图
    if(NULL==(G.vexs=(spot*)malloc(n*sizeof(spot)))) return OVERFLOW;
    for(i=0;i<G.n;i++) G.vexs[i]=vexs[i];
    //分配指针数组
    if(NULL==(G.arcs=(int **)malloc(n*sizeof(int*)))) 
        return OVERFLOW;
    //分配每个指针所指向的数组
	for(i=0;i<n;i++) 
        if(NULL==(G.arcs[i]=(int*)malloc(n*sizeof(int))))
            return OVERFLOW;
    if(NULL==(G.tags=(int*)malloc(n*sizeof(int)))) return OVERFLOW;
    //初始化标志数组和关系数组
	for(i=0;i<n;i++){   
        G.tags[i]=UNVISITED;
        for(j=0;j<n;j++) G.arcs[i][j]=info;
    }
    return OK;
}

 //创建含n个顶点和e条边的无向带权图图G，vexs为顶点信息，arcs为边信息
Status CreateGraph(MGraph &G,GraphKind kind,spot *vexs,int n,ArcInfo *arcs,int e){
    if(n<0||e<0||(n>0&&NULL==vexs)||(e>0&&NULL==arcs)) return ERROR;
    G.kind=kind;
    int i,j,k;
    spot v,w;
    //初始化
    if(InitGraph(G,vexs,n)!=OK) return ERROR;    
    G.e = e;//边数
	//建立关系数组
    for(k=0;k<G.e;k++){
        v=arcs[k].v; w=arcs[k].w;   //读入边(v,w)
        i=LocateVex(G,v);j=LocateVex(G,w);//确定v和w在顶点数组中的位序i和j
        if(i<0||j<0) return ERROR;
        G.arcs[i][j]=G.arcs[j][i]=arcs[k].info;
    }
    return OK;
}

 //求图G中k顶点的第一个邻接顶点的位序
Status FirstAdjVex(MGraph G,int k){
    int i;
    if(k<0||k>=G.n) return ERROR;
    //查找第一个值非零且非INFINITY的元素
    for(i=0;i<G.n;i++){
        if(G.arcs[k][i]!=0&&G.arcs[k][i]!=INFINITY) return i;
    }
    return ERROR;//k顶点无邻接顶点
}

 //m顶点为k顶点的邻接顶点，求图中k顶点相对于m顶点的下一个邻接顶点的位序
Status NextAdjVex(MGraph G,int k,int m){
    int i;
    if(k<0||k>=G.n||m<0||m>=G.n) return ERROR;
    for(i=m+1;i<G.n;i++)
        if(G.arcs[k][i]!=0&&G.arcs[k][i]!=INFINITY)
            return i;
    return ERROR;
}
 
 //求图G中从i顶点到其他所有顶点的最短路径，并由Dist返回
 //Dijkstra算法
Status Dijkstra(MGraph G,int i,DistInfo* &Dist){
    int j,m,k,min,p;
    Dist = (DistInfo*)malloc(G.n*sizeof(DistInfo));
    //初始化
    for(j=0;j<G.n;j++){
        Dist[j].lowcost = INFINITY;
        G.tags[j] = UNSELECTED;
    }
    //源点i引出的所有弧的信息存入Dist
    for(j=0;j<G.n;j++){
        if(G.arcs[i][j]!=INFINITY){
            Dist[j].prev=i;
            Dist[j].lowcost=G.arcs[i][j];
        }
    }
    Dist[i].prev=-1;Dist[i].lowcost=0;//源点i信息存入Dist
    G.tags[i]=SELECTED;//初始集合U仅含源点i
	//按路径长度升序，依次求源点到其他定点的最短路径
    for(m=1;m<G.n;m++){ 
        min=INFINITY;k=0;
        for(j=0;j<G.n;j++){
            if(UNSELECTED==G.tags[j]&&Dist[j].lowcost<min){
                k=j;
                min=Dist[k].lowcost;        //此处求得在V-U集合中的最短路径
            }
        }
        G.tags[k]=SELECTED; //将k顶点加入集合U
        //更新Dist数组
        for(p=FirstAdjVex(G,k);p>=0;p=NextAdjVex(G,k,p)){    
            if(UNSELECTED==G.tags[p]&&Dist[k].lowcost+G.arcs[k][p]<Dist[p].lowcost){
                Dist[p].lowcost = Dist[k].lowcost+G.arcs[k][p];     //k点的邻接点中距离最小的点p
                Dist[p].prev=k;
            }
        }
    }
    return 1;
}
 
 //沿Dist数组的prev域，可递归获得源点到k定点的最短路径
void Outputpath(MGraph G,DistInfo *Dist,int k){
    if(-1==k) return ;
    Outputpath(G,Dist,Dist[k].prev);//逆向递归获得路径上的顶点
    cout<<G.vexs[k].name<<"   ";//正向输出当前路径上的顶点
}



void creatVA(spot *vexs, ArcInfo *arcs){
 
    vexs[0].symbol=1;
    vexs[0].name="1鹅城音乐厅学术交流中心";
    vexs[0].introduction="每年总有精彩的节目在这里演出，这是展示惠院学子风采的地方!";
 
    vexs[1].symbol=2;
    vexs[1].name="2行政楼";
    vexs[1].introduction="作为学校的心脏，调动着上千个部门的运作，这是学校行政办公的地方";
 
    vexs[2].symbol=3;
    vexs[2].name="3旭日楼";
    vexs[2].introduction="最具特色的教学楼，是学子们思想交流与碰撞的地方";
 
    vexs[3].symbol=4;
    vexs[3].name="4叶竹君图书馆";
    vexs[3].introduction="惠院门面之一，浩瀚的书海让每个学子都流连忘返";
 
    vexs[4].symbol=5;
    vexs[4].name="5惠院正门";
    vexs[4].introduction="这里是惠院正门，走进校门就能感受到惠院学子的阆苑储英，人竞向学";
 
    vexs[5].symbol=6;
    vexs[5].name="6田径场";
    vexs[5].introduction="活力四射，激情澎湃，是惠院人的代名词，田径场是我们挥洒汗水，磨练自我的地方！";
 
    vexs[6].symbol=7;
    vexs[6].name="7中苑";
    vexs[6].introduction="一栋栋宿舍楼，这里是学生生活和居住的地方！";
 
    vexs[7].symbol=8;
    vexs[7].name="8田家炳大楼";
    vexs[7].introduction="田家炳先生捐赠的大楼助学子们圆梦!";
 
    vexs[8].symbol=9;
    vexs[8].name="9服装楼 化工楼 ";
    vexs[8].introduction="别具一格的服装楼和化工楼!";
 
    vexs[9].symbol=10;
    vexs[9].name="10快递站";
    vexs[9].introduction="菜鸟驿站，顺丰速运，智能柜等一应俱全，这便是学校的快递站！";
 
    vexs[10].symbol=11;
    vexs[10].name="11南苑";
    vexs[10].introduction="作为学校唯一有天桥连通的地方，这也是学生们的宿舍楼！";
 
    //边信息
    arcs[0].v=vexs[0];
    arcs[0].w=vexs[1];
    arcs[0].info=1;
 
    arcs[1].v=vexs[1];
    arcs[1].w=vexs[2];
    arcs[1].info=3;
 
    arcs[2].v=vexs[1];
    arcs[2].w=vexs[3];
    arcs[2].info=4;
 
    arcs[3].v=vexs[2];
    arcs[3].w=vexs[3];
    arcs[3].info=6;
 
    arcs[4].v=vexs[3];
    arcs[4].w=vexs[4];
    arcs[4].info=1;
 
    arcs[5].v=vexs[1];
    arcs[5].w=vexs[5];
    arcs[5].info=4;
 
    arcs[6].v=vexs[2];
    arcs[6].w=vexs[5];
    arcs[6].info=4;
 
    arcs[7].v=vexs[3];
    arcs[7].w=vexs[5];
    arcs[7].info=5;
 
    arcs[8].v=vexs[3];
    arcs[8].w=vexs[6];
    arcs[8].info=6;
 
    arcs[9].v=vexs[2];
    arcs[9].w=vexs[7];
    arcs[9].info=7;
 
    arcs[10].v=vexs[5];
    arcs[10].w=vexs[6];
    arcs[10].info=9;
 
    arcs[11].v=vexs[5];
    arcs[11].w=vexs[7];
    arcs[11].info=6;
 
    arcs[12].v=vexs[5];
    arcs[12].w=vexs[8];
    arcs[12].info=4;
 
    arcs[13].v=vexs[5];
    arcs[13].w=vexs[9];
    arcs[13].info=6;
 
    arcs[14].v=vexs[3];
    arcs[14].w=vexs[9];
    arcs[14].info=7;
 
    arcs[15].v=vexs[6];
    arcs[15].w=vexs[10];
    arcs[15].info=3;
 
    arcs[16].v=vexs[7];
    arcs[16].w=vexs[8];
    arcs[16].info=4;
 
    arcs[17].v=vexs[8];
    arcs[17].w=vexs[9];
    arcs[17].info=5;
 
    arcs[18].v=vexs[9];
    arcs[18].w=vexs[10];
    arcs[18].info=5;
 
}

 //访问结点信息（读取景点信息）
Status visit(int k,MGraph G){
    if(k<0||k>=G.n) return ERROR;
    cout<<"位置名字："<<G.vexs[k].name<<endl;
    cout<<"位置简介："<<G.vexs[k].introduction<<endl;
    return 1;
}

//修改位置信息
void reviseSpot(MGraph &G){ 
    int i,num;
    char *st;
    st=(char*)malloc(100*sizeof(char));
    cout<<"-----输入1修改位置名称，输入2修改位置简介-----"<<endl;
    cin>>i; 
    while(i!=1&&i!=2){
    	cout<<"-----对不起，你输入的数据有误，请重新输入-----"<<endl;
        cin>>i;
    }
    //修改名称
    if(1==i){           
    	cout<<"-----请输入位置序号-----"<<endl;
        cin>>num;
        while(num<=0||num>G.n){
        	cout<<"-----对不起，你输入的数据有误，请重新输入-----"<<endl;
            cin>>num;
        }
        cout<<"-----请输入修改后的位置名称-----"<<endl;
        cin>>st;
        G.vexs[num-1].name=st;
    }
    //修改简介
    else {             
    	cout<<"-----请输入位置序号-----"<<endl;
        cin>>num;
        while(num<=0||num>G.n){
        	cout<<"-----对不起，你输入的数据有误，请重新输入-----"<<endl;
            cin>>num;
        }
        cout<<"-----请输入修改后的位置简介-----"<<endl;
        cin>>st;
        G.vexs[num-1].introduction=st;
    }
    cout<<"-----修改成功-----"<<endl;
}

void menu(){
    cout<<"\t\t\t     惠州学院导航系统菜单      \n";
    cout<<"\t\t\t-----------------------------\n";
    cout<<"\t\t\t                             \n";
    cout<<"\t\t\t  1--显示菜单                \n";
    cout<<"\t\t\t  2--显示地图                \n";
    cout<<"\t\t\t  3--显示位置具体信息        \n";
    cout<<"\t\t\t  4--修改位置信息            \n";
    cout<<"\t\t\t  5--寻找两位置间最短路径    \n";
    cout<<"\t\t\t  0--退出系统                \n";
    cout<<"\t\t\t                             \n";
    cout<<"\t\t\t-----------------------------\n";
}
 
void printmap(MGraph &G){
    cout<<"\n\t\t                        地图                         \n\n";
    cout<<"\t "<<G.vexs[10].name<<"-----------"<<G.vexs[9].name<<"-----------"<<G.vexs[8].name<<"-----------"<<G.vexs[7].name<<endl;
    cout<<"\t  |   "<<G.arcs[10][9]<<"00米     |#       "<<G.arcs[9][8]<<"00米 |             #|    "<<G.arcs[8][7]<<"00米   "<<endl;
    cout<<"\t  |             | #            |            # |  "<<endl;
    cout<<"\t  |             |  # "<<G.arcs[9][5]<<"00米     |     "<<G.arcs[7][5]<<"00米 #  |  "<<endl;
    cout<<"\t  |"<<G.arcs[10][6]<<"00米   "<<G.arcs[9][3]<<"00米|   ######"<<G.arcs[8][5]<<"00米|    #######   |"<<G.arcs[7][2]<<"00米"<<endl;
    cout<<"\t  |             |         #    |   #          |  "<<endl;
    cout<<"\t  |             |          #   |  #           |  "<<endl;
    cout<<"\t"<<G.vexs[6].name<<"-----------|-----------"<<G.vexs[5].name<<"           |  "<<endl;
    cout<<"\t   #    "<<G.arcs[6][5]<<"00米   |            # | #            |  "<<endl;
    cout<<"\t    #           |     "<<G.arcs[5][3]<<"00米 #  |  #  "<<G.arcs[5][2]<<"00米    |  "<<endl;
    cout<<"\t     # "<<G.arcs[6][3]<<"00米    |   ########   |   ########   |  "<<endl;
    cout<<"\t      ########  |  #      "<<G.arcs[5][2]<<"00米|           #  |  "<<endl;
    cout<<"\t              # | #            |            # |  "<<endl;
    cout<<"\t               #|#      "<<G.arcs[3][2]<<"00米  |              |  "<<endl;
    cout<<"\t           "<<G.vexs[3].name<<"-------|------------"<<G.vexs[2].name<<endl;
    cout<<"\t               # #             |             #   "<<endl;
    cout<<"\t        "<<G.arcs[3][4]<<"00米 #   ###########  |    #########    "<<endl;
    cout<<"\t             #     "<<G.arcs[3][1]<<"00米     # |   #   "<<G.arcs[2][1]<<"00米"<<endl;
    cout<<"\t          "<<G.vexs[4].name<<"          "<<G.vexs[1].name<<"              \n";
    cout<<"\t                               |                 \n";
    cout<<"\t                               |"<<G.arcs[1][0]<<"00米             \n";
    cout<<"\t                     "<<G.vexs[0].name<<"             \n";
  
}
 
int main(){
    int n=11,e=19,sum=0,flag=0;
    spot *vexs;
    ArcInfo *arcs;
    int *path;      //用于存储路径
    int length;     //当前路径长度
    vexs=(spot*)malloc(n*sizeof(spot));         //分配空间
    arcs=(ArcInfo*)malloc(e*sizeof(ArcInfo));
    path=(int*)malloc(e*sizeof(int));
    length=0;
    MGraph G;
    DistInfo *Dist; //定义数组
    creatVA(vexs,arcs);
    CreateGraph(G,UDN,vexs,n,arcs,e);
	int choice=INFINITY,i,j;
    cout<<"\t\t欢迎使用惠州学院导航系统，菜单与地图如下：\n\n";
    menu();
	printmap(G);
	cout<<endl; 
    while(choice){
        cout<<"\n*******请根据导航系统菜单输入指令*******\n";
        	cin>>choice;
            switch(choice)
            {
                case 3:
                        cout<<"-----请输入被查看位置的序号-----\n";
                        cin>>i;
                        while(i<=0||i>G.n){
                            cout<<"-----对不起，你输入的数据有误，请重新输入-----\n";
                            cin>>i;
                        }
                        visit(i-1,G);
                        break;
                case 5:
                        for(i=0;i<n;i++){   //初始化标志数组
                            G.tags[i]=UNVISITED;
                        }
                        cout<<"-----请输入第一个位置的序号-----\n";      //算最短路径
                        cin>>i;
                        while(i<=0||i>G.n){
                            cout<<"-----对不起，你输入的数据有误，请重新输入-----\n";
                            cin>>i;
                        }
                        cout<<"-----请输入第二个位置的序号-----\n";
                        cin>>j;
                        while(j<=0||j>G.n){
                            cout<<"-----对不起，你输入的数据有误，请重新输入-----\n";
                            cin>>j;
                        }
                        Dijkstra(G,i-1,Dist);   //迪杰斯特拉算法求出Dist数组
                        if(Dist[j-1].lowcost==INFINITY){
                            cout<<"-----对不起,你输入的两个位置间不存在道路-----\n";
                            break;
                        }else{
                        cout<<"最短路线：";
                        Outputpath(G,Dist,j-1); //递归输出
                        cout<<endl;
                        cout<<"最短路径长度为:"<<Dist[j-1].lowcost*100<<"米\n";
                        break;
                        }
                case 1:
                        menu();break;
                case 2:
                        printmap(G);break;
                case 4:
                        reviseSpot(G);break;
                case 0:
                        cout<<"-----系统已退出，欢迎下次继续体验-----\n";
                        break;
                default:
                        cout<<"-----对不起，你输入的数据有误，请重新输入-----\n";break;
            }
    }
    return 0;
}

