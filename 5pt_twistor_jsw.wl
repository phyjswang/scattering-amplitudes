(* ::Package:: *)

\[Sigma][0]=({
 {1, 0},
 {0, 1}
});
\[Sigma][1]=({
 {0, 1},
 {1, 0}
});
\[Sigma][2]=({
 {0, -I},
 {I, 0}
});
\[Sigma][3]=({
 {1, 0},
 {0, -1}
});
sigma=Table[\[Sigma][i],{i,0,3}];
mp[v1_,v2_]:=-v1.v2+2 v1[[1]] v2[[1]];
mp2[v1_]:=mp[v1,v1];
epsilonup=({
 {0, 1},
 {-1, 0}
});
epsilondown=-epsilonup;

Flag=1;   (* !!! *)
aa[\[Lambda]1_,\[Lambda]2_]:=Flag*\[Lambda]1.epsilondown.\[Lambda]2;
bb[\[Lambda]1t_,\[Lambda]2t_]:=Flag*\[Lambda]1t.epsilonup.\[Lambda]2t;
vM[\[Lambda]_,\[Lambda]t_]:=Transpose[{\[Lambda]}].{\[Lambda]t};
v[\[Lambda]1_,\[Lambda]t1_]:=Module[{\[Lambda]=\[Lambda]1,\[Lambda]t=\[Lambda]t1,matrix,p0,p1,p2,p3,p,ss},
p={p0,p1,p2,p3};
ss=Solve[vM[\[Lambda],\[Lambda]t]==p.sigma,p];
Return[p/.ss[[1]]];
];
newv[\[Lambda]1_,\[Lambda]2t_]:=Module[{\[Lambda]=\[Lambda]1,\[Lambda]pt=\[Lambda]2t,result},
result=Table[1/2 \[Lambda]pt.\[Sigma][i].\[Lambda],{i,0,3}];
Return[result]];


\[Lambda][1]= {1,0};
\[Lambda][2]={0,1};
\[Lambda][3]={1/x1,1};
\[Lambda][4]={1/x2+1/x1,1};
\[Lambda][5]={1/x3+1/x2+1/x1,1};
\[Mu][1]={0,0};
\[Mu][2]={0,0};
\[Mu][3]={0,1};
\[Mu][4]={x4,1};
\[Mu][5]={1,x5/x4};


sRules={s13->-s12-s23+s45,s14->-s15+s23-s45,s24->s15-s23-s34,s25->-s12-s15+s34,s35->s12-s34-s45};


lambda={\[Lambda][1],\[Lambda][2],\[Lambda][3],\[Lambda][4],\[Lambda][5]};
mu={\[Mu][1],\[Mu][2],\[Mu][3],\[Mu][4],\[Mu][5]};
lambdat=Table[0,{j,1,5}];
For[i=1,i<=5,i++,
ip=i+1;
If[ip>5,ip-=5];
im=i-1;
If[im<=0,im+=5];

lambdat[[i]]=1/(aa[\[Lambda][im],\[Lambda][i]] aa[\[Lambda][i],\[Lambda][ip]] ) (aa[\[Lambda][im],\[Lambda][i]] \[Mu][ip]+aa[\[Lambda][i],\[Lambda][ip]] \[Mu][im]+aa[\[Lambda][ip],\[Lambda][im]] \[Mu][i]);

]
{\[Lambda]t[1],\[Lambda]t[2],\[Lambda]t[3],\[Lambda]t[4],\[Lambda]t[5]}=lambdat//Simplify
P=Table[v[\[Lambda][j],\[Lambda]t[j]],{j,1,5}]//Simplify
Sum[v[\[Lambda][j],\[Lambda]t[j]],{j,1,5}]//Simplify

AA[i_,j_]:=aa[\[Lambda][i],\[Lambda][j]];
BB[i_,j_]:=bb[\[Lambda]t[i],\[Lambda]t[j]];


Table[AA[i,j],{i,1,5},{j,1,5}]//FullSimplify//MatrixForm;
listMP[l1_,l2_]:=Module[{list1=l1,list2=l2,i,j,n1,n2,result=0,ip1,ip2},
n1=Length[list1]/3;
n2=Length[list2]/3;

For[i=1,i<=n1,i++,
For[j=1,j<=n2,j++,
ip1=(i-1)*3+1;
ip2=(j-1)*3+1;
result+=list1[[ip1]] list2[[ip2]] AA[list1[[ip1+1]],list2[[ip2+1]]] BB[list2[[ip2+2]],list1[[ip1+2]]]/2;

];
];

Return[result];
];
Gram5=Table[mp[P[[i]],P[[j]]],{i,1,5},{j,1,5}]//FullSimplify;
2%//MatrixForm
Gram5//ByteCount
ss=Solve[{s12==2 Gram5[[1,2]],s23==2 Gram5[[2,3]],s34==2 Gram5[[3,4]],s45==2Gram5[[4,5]],s15==2Gram5[[1,5]]},{x1,x2,x3,x4,x5}]//Simplify


VV[x_,y_]:=v[\[Lambda][x],\[Lambda]t[y]];


Gram4=Table[mp[P[[i]],P[[j]]],{i,1,4},{j,1,4}]//FullSimplify;
G4=Det[2Gram4]//FullSimplify;
tr5=4I Det[{P[[1]],P[[2]],P[[3]],P[[4]]}]//FullSimplify;
tr5^2==G4//FullSimplify
GG4=Det[({
 {0, s12, s13, s14},
 {s12, 0, s23, s24},
 {s13, s23, 0, s34},
 {s14, s24, s34, 0}
})]//.sRules//Simplify;
GG4==4 s12 s23 s34 (s15-s23+s45)+(s12 (-s15+s23)+s23 s34+(s15-s34) s45)^2//Simplify
ss=ss/.{\[Sqrt](4 s12 s23 s34 (s15-s23+s45)+(s12 (-s15+s23)+s23 s34+(s15-s34) s45)^2)->Tr5};



rReduce[exp1_]:=Module[{exp=exp1,list,i,n,sq},
list=MonomialList[exp,Tr5];

For[i=1,i<=Length[list],i++,
If[list[[i]]==0,Continue[]];
n=Exponent[list[[i]],Tr5];
sq=Floor[n/2];
list[[i]]=list[[i]]/.Tr5->1;
list[[i]]*=(GG4)^sq;
list[[i]]*=Tr5^(n-sq*2);
];

Return[Total[list]];

];
ReduceFraction[exp1_]:=Module[{exp=exp1,A,B,test,a,b,c,d,num,den},
If[exp==0,Return[0]];

test=exp;

test=test/.ss[[2]]//Together;



A=rReduce[Numerator[test]];
B=rReduce[Denominator[test]];



a=Coefficient[A,Tr5,1];
b=Coefficient[A,Tr5,0];
c=Coefficient[B,Tr5,1];
d=Coefficient[B,Tr5,0];
num=rReduce[(a Tr5+b)(c Tr5-d)];
den=c^2 GG4-d^2;
Return[num/den]; 
];


S[i_,j_]:=2 Gram5[[i,j]];


numericX={x1->1,x2->3,x3->5,x4->7,x5->11};
