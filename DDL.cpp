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
typedef enum{DG,DN,UDG,UDN} GraphKind;   //ͼ���������ͣ�����ͼ�������Ȩͼ������ͼ�������Ȩͼ

typedef struct{
    int symbol;//λ�ô���
    char *name;//λ������
    char *introduction;//λ�ü��
}spot;          //λ������
 
typedef struct{
    spot v,w;   //�ߵĶ˵�
    int info;   //�Դ�Ȩͼ��ΪȨֵ���˴�Ϊ����
}ArcInfo;   //�洢����Ϣ
 
typedef struct{
    spot *vexs;  //�������飬spot��λ������
    int **arcs;  //��ϵ���飬��ͼΪ��Ȩͼ����ΪȨֵ��INFINITY
    int n,e;     //�������ͱ���
    GraphKind kind;//   ͼ������
    int *tags;   //��־���飬��������ͼ�ı����б�Ƕ���������
}MGraph;    
 
typedef struct{
    int prev;   //��ǰ���·���ϸö����ǰ�������λ��
    int lowcost;//��ǰ���·���ĳ���
}DistInfo;
 
 //���ݶ��㱾�����ݣ��жϳ������ڶ�ά�����е�λ��
Status LocateVex(MGraph G,spot v){
    int i;
    for(i=0;i<G.n;i++)
        if(v.symbol==G.vexs[i].symbol) return i;
    return ERROR;
}
 //��ʼ����n���������ޱߵ�kind���ͼG
Status InitGraph(MGraph &G,spot *vexs,int n){
    int i,j,info;
    if(n<0||(n>0&&NULL==vexs)) return ERROR;
    if(G.kind!=UDN) return ERROR;
    info=INFINITY;  //��Ȩͼ
    G.n = n;
    G.e = 0;  //�������ͱ���
    if(0==G.n) return OK;   //��ͼ
    if(NULL==(G.vexs=(spot*)malloc(n*sizeof(spot)))) return OVERFLOW;
    for(i=0;i<G.n;i++) G.vexs[i]=vexs[i];
    //����ָ������
    if(NULL==(G.arcs=(int **)malloc(n*sizeof(int*)))) 
        return OVERFLOW;
    //����ÿ��ָ����ָ�������
	for(i=0;i<n;i++) 
        if(NULL==(G.arcs[i]=(int*)malloc(n*sizeof(int))))
            return OVERFLOW;
    if(NULL==(G.tags=(int*)malloc(n*sizeof(int)))) return OVERFLOW;
    //��ʼ����־����͹�ϵ����
	for(i=0;i<n;i++){   
        G.tags[i]=UNVISITED;
        for(j=0;j<n;j++) G.arcs[i][j]=info;
    }
    return OK;
}

 //������n�������e���ߵ������ȨͼͼG��vexsΪ������Ϣ��arcsΪ����Ϣ
Status CreateGraph(MGraph &G,GraphKind kind,spot *vexs,int n,ArcInfo *arcs,int e){
    if(n<0||e<0||(n>0&&NULL==vexs)||(e>0&&NULL==arcs)) return ERROR;
    G.kind=kind;
    int i,j,k;
    spot v,w;
    //��ʼ��
    if(InitGraph(G,vexs,n)!=OK) return ERROR;    
    G.e = e;//����
	//������ϵ����
    for(k=0;k<G.e;k++){
        v=arcs[k].v; w=arcs[k].w;   //�����(v,w)
        i=LocateVex(G,v);j=LocateVex(G,w);//ȷ��v��w�ڶ��������е�λ��i��j
        if(i<0||j<0) return ERROR;
        G.arcs[i][j]=G.arcs[j][i]=arcs[k].info;
    }
    return OK;
}

 //��ͼG��k����ĵ�һ���ڽӶ����λ��
Status FirstAdjVex(MGraph G,int k){
    int i;
    if(k<0||k>=G.n) return ERROR;
    //���ҵ�һ��ֵ�����ҷ�INFINITY��Ԫ��
    for(i=0;i<G.n;i++){
        if(G.arcs[k][i]!=0&&G.arcs[k][i]!=INFINITY) return i;
    }
    return ERROR;//k�������ڽӶ���
}

 //m����Ϊk������ڽӶ��㣬��ͼ��k���������m�������һ���ڽӶ����λ��
Status NextAdjVex(MGraph G,int k,int m){
    int i;
    if(k<0||k>=G.n||m<0||m>=G.n) return ERROR;
    for(i=m+1;i<G.n;i++)
        if(G.arcs[k][i]!=0&&G.arcs[k][i]!=INFINITY)
            return i;
    return ERROR;
}
 
 //��ͼG�д�i���㵽�������ж�������·��������Dist����
 //Dijkstra�㷨
Status Dijkstra(MGraph G,int i,DistInfo* &Dist){
    int j,m,k,min,p;
    Dist = (DistInfo*)malloc(G.n*sizeof(DistInfo));
    //��ʼ��
    for(j=0;j<G.n;j++){
        Dist[j].lowcost = INFINITY;
        G.tags[j] = UNSELECTED;
    }
    //Դ��i���������л�����Ϣ����Dist
    for(j=0;j<G.n;j++){
        if(G.arcs[i][j]!=INFINITY){
            Dist[j].prev=i;
            Dist[j].lowcost=G.arcs[i][j];
        }
    }
    Dist[i].prev=-1;Dist[i].lowcost=0;//Դ��i��Ϣ����Dist
    G.tags[i]=SELECTED;//��ʼ����U����Դ��i
	//��·����������������Դ�㵽������������·��
    for(m=1;m<G.n;m++){ 
        min=INFINITY;k=0;
        for(j=0;j<G.n;j++){
            if(UNSELECTED==G.tags[j]&&Dist[j].lowcost<min){
                k=j;
                min=Dist[k].lowcost;        //�˴������V-U�����е����·��
            }
        }
        G.tags[k]=SELECTED; //��k������뼯��U
        //����Dist����
        for(p=FirstAdjVex(G,k);p>=0;p=NextAdjVex(G,k,p)){    
            if(UNSELECTED==G.tags[p]&&Dist[k].lowcost+G.arcs[k][p]<Dist[p].lowcost){
                Dist[p].lowcost = Dist[k].lowcost+G.arcs[k][p];     //k����ڽӵ��о�����С�ĵ�p
                Dist[p].prev=k;
            }
        }
    }
    return 1;
}
 
 //��Dist�����prev�򣬿ɵݹ���Դ�㵽k��������·��
void Outputpath(MGraph G,DistInfo *Dist,int k){
    if(-1==k) return ;
    Outputpath(G,Dist,Dist[k].prev);//����ݹ���·���ϵĶ���
    cout<<G.vexs[k].name<<"   ";//���������ǰ·���ϵĶ���
}



void creatVA(spot *vexs, ArcInfo *arcs){
 
    vexs[0].symbol=1;
    vexs[0].name="1���������ѧ����������";
    vexs[0].introduction="ÿ�����о��ʵĽ�Ŀ�������ݳ�������չʾ��Ժѧ�ӷ�ɵĵط�!";
 
    vexs[1].symbol=2;
    vexs[1].name="2����¥";
    vexs[1].introduction="��ΪѧУ�����࣬��������ǧ�����ŵ�����������ѧУ�����칫�ĵط�";
 
    vexs[2].symbol=3;
    vexs[2].name="3����¥";
    vexs[2].introduction="�����ɫ�Ľ�ѧ¥����ѧ����˼�뽻������ײ�ĵط�";
 
    vexs[3].symbol=4;
    vexs[3].name="4Ҷ���ͼ���";
    vexs[3].introduction="��Ժ����֮һ����嫵��麣��ÿ��ѧ�Ӷ���������";
 
    vexs[4].symbol=5;
    vexs[4].name="5��Ժ����";
    vexs[4].introduction="�����ǻ�Ժ���ţ��߽�У�ž��ܸ��ܵ���Ժѧ�ӵ���Է��Ӣ���˾���ѧ";
 
    vexs[5].symbol=6;
    vexs[5].name="6�ﾶ��";
    vexs[5].introduction="�������䣬�������ȣ��ǻ�Ժ�˵Ĵ����ʣ��ﾶ�������ǻ�����ˮ��ĥ�����ҵĵط���";
 
    vexs[6].symbol=7;
    vexs[6].name="7��Է";
    vexs[6].introduction="һ��������¥��������ѧ������;�ס�ĵط���";
 
    vexs[7].symbol=8;
    vexs[7].name="8��ұ���¥";
    vexs[7].introduction="��ұ����������Ĵ�¥��ѧ����Բ��!";
 
    vexs[8].symbol=9;
    vexs[8].name="9��װ¥ ����¥ ";
    vexs[8].introduction="���һ��ķ�װ¥�ͻ���¥!";
 
    vexs[9].symbol=10;
    vexs[9].name="10���վ";
    vexs[9].introduction="������վ��˳�����ˣ����ܹ��һӦ��ȫ�������ѧУ�Ŀ��վ��";
 
    vexs[10].symbol=11;
    vexs[10].name="11��Է";
    vexs[10].introduction="��ΪѧУΨһ��������ͨ�ĵط�����Ҳ��ѧ���ǵ�����¥��";
 
    //����Ϣ
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

 //���ʽ����Ϣ����ȡ������Ϣ��
Status visit(int k,MGraph G){
    if(k<0||k>=G.n) return ERROR;
    cout<<"λ�����֣�"<<G.vexs[k].name<<endl;
    cout<<"λ�ü�飺"<<G.vexs[k].introduction<<endl;
    return 1;
}

//�޸�λ����Ϣ
void reviseSpot(MGraph &G){ 
    int i,num;
    char *st;
    st=(char*)malloc(100*sizeof(char));
    cout<<"-----����1�޸�λ�����ƣ�����2�޸�λ�ü��-----"<<endl;
    cin>>i; 
    while(i!=1&&i!=2){
    	cout<<"-----�Բ����������������������������-----"<<endl;
        cin>>i;
    }
    //�޸�����
    if(1==i){           
    	cout<<"-----������λ�����-----"<<endl;
        cin>>num;
        while(num<=0||num>G.n){
        	cout<<"-----�Բ����������������������������-----"<<endl;
            cin>>num;
        }
        cout<<"-----�������޸ĺ��λ������-----"<<endl;
        cin>>st;
        G.vexs[num-1].name=st;
    }
    //�޸ļ��
    else {             
    	cout<<"-----������λ�����-----"<<endl;
        cin>>num;
        while(num<=0||num>G.n){
        	cout<<"-----�Բ����������������������������-----"<<endl;
            cin>>num;
        }
        cout<<"-----�������޸ĺ��λ�ü��-----"<<endl;
        cin>>st;
        G.vexs[num-1].introduction=st;
    }
    cout<<"-----�޸ĳɹ�-----"<<endl;
}

void menu(){
    cout<<"\t\t\t     ����ѧԺ����ϵͳ�˵�      \n";
    cout<<"\t\t\t-----------------------------\n";
    cout<<"\t\t\t                             \n";
    cout<<"\t\t\t  1--��ʾ�˵�                \n";
    cout<<"\t\t\t  2--��ʾ��ͼ                \n";
    cout<<"\t\t\t  3--��ʾλ�þ�����Ϣ        \n";
    cout<<"\t\t\t  4--�޸�λ����Ϣ            \n";
    cout<<"\t\t\t  5--Ѱ����λ�ü����·��    \n";
    cout<<"\t\t\t  0--�˳�ϵͳ                \n";
    cout<<"\t\t\t                             \n";
    cout<<"\t\t\t-----------------------------\n";
}
 
void printmap(MGraph &G){
    cout<<"\n\t\t                        ��ͼ                         \n\n";
    cout<<"\t "<<G.vexs[10].name<<"-----------"<<G.vexs[9].name<<"-----------"<<G.vexs[8].name<<"-----------"<<G.vexs[7].name<<endl;
    cout<<"\t  |   "<<G.arcs[10][9]<<"00��     |#       "<<G.arcs[9][8]<<"00�� |             #|    "<<G.arcs[8][7]<<"00��   "<<endl;
    cout<<"\t  |             | #            |            # |  "<<endl;
    cout<<"\t  |             |  # "<<G.arcs[9][5]<<"00��     |     "<<G.arcs[7][5]<<"00�� #  |  "<<endl;
    cout<<"\t  |"<<G.arcs[10][6]<<"00��   "<<G.arcs[9][3]<<"00��|   ######"<<G.arcs[8][5]<<"00��|    #######   |"<<G.arcs[7][2]<<"00��"<<endl;
    cout<<"\t  |             |         #    |   #          |  "<<endl;
    cout<<"\t  |             |          #   |  #           |  "<<endl;
    cout<<"\t"<<G.vexs[6].name<<"-----------|-----------"<<G.vexs[5].name<<"           |  "<<endl;
    cout<<"\t   #    "<<G.arcs[6][5]<<"00��   |            # | #            |  "<<endl;
    cout<<"\t    #           |     "<<G.arcs[5][3]<<"00�� #  |  #  "<<G.arcs[5][2]<<"00��    |  "<<endl;
    cout<<"\t     # "<<G.arcs[6][3]<<"00��    |   ########   |   ########   |  "<<endl;
    cout<<"\t      ########  |  #      "<<G.arcs[5][2]<<"00��|           #  |  "<<endl;
    cout<<"\t              # | #            |            # |  "<<endl;
    cout<<"\t               #|#      "<<G.arcs[3][2]<<"00��  |              |  "<<endl;
    cout<<"\t           "<<G.vexs[3].name<<"-------|------------"<<G.vexs[2].name<<endl;
    cout<<"\t               # #             |             #   "<<endl;
    cout<<"\t        "<<G.arcs[3][4]<<"00�� #   ###########  |    #########    "<<endl;
    cout<<"\t             #     "<<G.arcs[3][1]<<"00��     # |   #   "<<G.arcs[2][1]<<"00��"<<endl;
    cout<<"\t          "<<G.vexs[4].name<<"          "<<G.vexs[1].name<<"              \n";
    cout<<"\t                               |                 \n";
    cout<<"\t                               |"<<G.arcs[1][0]<<"00��             \n";
    cout<<"\t                     "<<G.vexs[0].name<<"             \n";
  
}
 
int main(){
    int n=11,e=19,sum=0,flag=0;
    spot *vexs;
    ArcInfo *arcs;
    int *path;      //���ڴ洢·��
    int length;     //��ǰ·������
    vexs=(spot*)malloc(n*sizeof(spot));         //����ռ�
    arcs=(ArcInfo*)malloc(e*sizeof(ArcInfo));
    path=(int*)malloc(e*sizeof(int));
    length=0;
    MGraph G;
    DistInfo *Dist; //��������
    creatVA(vexs,arcs);
    CreateGraph(G,UDN,vexs,n,arcs,e);
	int choice=INFINITY,i,j;
    cout<<"\t\t��ӭʹ�û���ѧԺ����ϵͳ���˵����ͼ���£�\n\n";
    menu();
	printmap(G);
	cout<<endl; 
    while(choice){
        cout<<"\n*******����ݵ���ϵͳ�˵�����ָ��*******\n";
        	cin>>choice;
            switch(choice)
            {
                case 3:
                        cout<<"-----�����뱻�鿴λ�õ����-----\n";
                        cin>>i;
                        while(i<=0||i>G.n){
                            cout<<"-----�Բ����������������������������-----\n";
                            cin>>i;
                        }
                        visit(i-1,G);
                        break;
                case 5:
                        for(i=0;i<n;i++){   //��ʼ����־����
                            G.tags[i]=UNVISITED;
                        }
                        cout<<"-----�������һ��λ�õ����-----\n";      //�����·��
                        cin>>i;
                        while(i<=0||i>G.n){
                            cout<<"-----�Բ����������������������������-----\n";
                            cin>>i;
                        }
                        cout<<"-----������ڶ���λ�õ����-----\n";
                        cin>>j;
                        while(j<=0||j>G.n){
                            cout<<"-----�Բ����������������������������-----\n";
                            cin>>j;
                        }
                        Dijkstra(G,i-1,Dist);   //�Ͻ�˹�����㷨���Dist����
                        if(Dist[j-1].lowcost==INFINITY){
                            cout<<"-----�Բ���,�����������λ�ü䲻���ڵ�·-----\n";
                            break;
                        }else{
                        cout<<"���·�ߣ�";
                        Outputpath(G,Dist,j-1); //�ݹ����
                        cout<<endl;
                        cout<<"���·������Ϊ:"<<Dist[j-1].lowcost*100<<"��\n";
                        break;
                        }
                case 1:
                        menu();break;
                case 2:
                        printmap(G);break;
                case 4:
                        reviseSpot(G);break;
                case 0:
                        cout<<"-----ϵͳ���˳�����ӭ�´μ�������-----\n";
                        break;
                default:
                        cout<<"-----�Բ����������������������������-----\n";break;
            }
    }
    return 0;
}

