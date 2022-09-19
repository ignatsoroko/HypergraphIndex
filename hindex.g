#
# The GAP code for computing hypergraph index, accompanying the article 
# "Divergence, thickness and hypergraph index for general Coxeter groups"
# by Pallavi Dani, Yusra Naqvi, Ignat Soroko, and Anne Thomas, 2022
# 
# For all questions or comments about this code, contact Ignat Soroko at ignat.soroko@gmail.com
#

#
# Convention:
# if M is a Coxeter matrix, then M[i][j]=M[j][i], M[i][i]=1; infinity is represented by 0
#


# input: a Coxeter matrix M
# output: the list of colors of vertices, corresponding to connected components
# see function "DirectProductDecomposition" below
# sep = 0 or 2 encodes disconnectedness:
# if sep=2 then we are in Dynkin notation: M[i][j]=2 means vertices i and j are disconnected in a Dynkin diagram;
# if sep=0 then we are in general Coxeter notation (or RACGs): M[i][j]=0 corresponds to vertices i and j being disconnected (0 stands for infinity)
# upd: name changed to 'ConnComponents' to avoid conflict with 'grape' package
ConnComponents:=function(M,sep)
	local C,c,n,i,j,k,m,c0;
	
	n:=Size(M); # number of vertices in the whole Dynkin diagram
	C:=List([1..n],i->0); # initializing the list of colors, 0 means unvisited vertex
	m:=0; # m is the number of colors involved so far

	for i in [1..n] do
		# looping over vertices and checking connections
		
		if C[i]=0 then m:=m+1; C[i]:=m; fi; # a new color for an unvisited vertex
		
		c:=C[i]; # the color of the current vertex
		
		for j in [i+1..n] do
			if M[i][j]<>sep then  # if vertices i and j are connected by a non-sep label
				if C[j]=c then continue; fi; # j-th vertex already has same color as i-th, do nothing
				if C[j]=0 then C[j]:=c; continue; fi; # if j-th vertex is unvisited, paint it in the color of i-th vertex
				
				# now C[j] is different from c and non-zero
				
				# if j-th vertex color is bigger than the i-th one, 
				# we repaint the whole component of j-th vertex into i-th color
				if C[j]>c then
					c0:=C[j];
					for k in [1..n] do 
						if C[k]=c0 then C[k]:=c; fi;
					od;
					continue;
				fi;
					
				# now C[j]<c and we need to repaint the whole component of i-th vertex
				# into the color of j-th vertex
				c0:=C[j];
				for k in [1..n] do
					if C[k]=c then C[k]:=c0; fi;
				od;
				c:=c0;  # now the current color is c0
			fi;
		od;
	od;
	return C;
end;


# input: a Coxeter matrix M, a subset T of [1..Size(M)]
# output: the submatrix of M with rows and columns from T
CoxeterSubmatrix:=function(M,T)
	local i,j,m,n,k;
	
	n:=Size(T); 
	m:=List([1..n],i->[]); # a new Coxeter matrix
	for i in [1..n] do for j in [1..n] do
		m[i][j]:=M[T[i]][T[j]];
	od;od;
	return m;
end;


# input: a Coxeter matrix M
# output: a list of subsets of [1..Size(M)] corresponding to Dynkin-indecomposable subsystems
DirectProductDecomposition:=function(M)
	local C,U,i,L,res,x;

	C:=ConnComponents(M,2); # 2 encodes disconnectedness of vertices in the Dynkin diagram
	U:=Unique(C);
	L:=List(U,i->Positions(C,i));
	#res:=List(L,x->CoxeterSubmatrix(M,x));
	#return res;
	return L;
end;

# forms a join (direct sum) of Coxeter matrices lst=[m1,...,ms]
JoinOfCoxeterMatrices:=function(lst)
	local M,i,j,n,k,m;

	n:=Sum(lst,Size);
	M:=NullMat(n,n)+2-IdentityMat(n);
	k:=0;
	for m in lst do
		for i in [1..Size(m)] do for j in [1..Size(m)] do
			M[k+i][k+j]:=m[i][j];
		od;od;
		k:=k+Size(m);
	od;
	return M;
end;


# Action of Sym(n) on matrices
# M is nxn matrix, g is a permutation from Sym(n)
OnMatrices:=function(M,g)
	local x;
	return Permuted(List(M,x->Permuted(x,g)),g);
end;

CoxeterMatrixAn:=function(n)
	local m,i;
	if not IsInt(n) or n<1 then return fail; fi;
	m:=NullMat(n,n)+2-IdentityMat(n);
	for i in [1..n-1] do m[i][i+1]:=3; m[i+1][i]:=3; od;
	return m;
end;

CoxeterMatrixBn:=function(n)
	local m,i;
	if not IsInt(n) or n<2 then return fail; fi;
	m:=NullMat(n,n)+2-IdentityMat(n);
	for i in [1..n-2] do m[i][i+1]:=3; m[i+1][i]:=3; od;
	m[n-1][n]:=4; m[n][n-1]:=4;
	return m;
end;

CoxeterMatrixCn:=function(n)
	return CoxeterMatrixBn(n);
end;

CoxeterMatrixDn:=function(n)
	local m,i;
	if not IsInt(n) or n<2 then return fail; fi;
	m:=NullMat(n,n)+2-IdentityMat(n);
	for i in [1..n-2] do m[i][i+1]:=3; m[i+1][i]:=3; od;
	if n>2 then m[n-2][n]:=3; m[n][n-2]:=3; fi;
	return m;
end;

CoxeterMatrixEn:=function(n) # Bourbaki's numeration of vertices (leaves: 1,2,n, branch at 4)
	local m,i;
	if not n in [6,7,8] then return fail; fi;
	m:=NullMat(n,n)+2-IdentityMat(n);	
	for i in [3..n-1] do m[i][i+1]:=3; m[i+1][i]:=3; od;
	m[1][3]:=3; m[3][1]:=3; 
	m[2][4]:=3; m[4][2]:=3;
	return m;
end;

CoxeterMatrixFn:=function(n) 
	local m,i;
	if not n=4 then return fail; fi;
	m:=NullMat(n,n)+2-IdentityMat(n);	
	for i in [1..n-1] do m[i][i+1]:=3; m[i+1][i]:=3; od;
	m[2][3]:=4; m[3][2]:=4;	
	return m;
end;

CoxeterMatrixHn:=function(n) # label 5 on 1-2 edge
	local m,i;
	if not n in [2,3,4] then return fail; fi;
	m:=NullMat(n,n)+2-IdentityMat(n);	
	for i in [1..n-1] do m[i][i+1]:=3; m[i+1][i]:=3; od;
	m[1][2]:=5; m[2][1]:=5;	
	return m;
end;

CoxeterMatrixI2m:=function(a) 
	local m;
	if not IsInt(a) or a=1 then return fail; fi;
	m:=[[1,a],[a,1]];
	return m;
end;

CoxeterMatrixGn:=function(n) 
	if not n=2 then return fail; fi;
	return CoxeterMatrixI2m(6);
end;


CoxeterMatrixAffineAn_:=function(n)
	local m,i;
	if not IsInt(n) or n<2 then return fail; fi;
	m:=NullMat(n,n)+2-IdentityMat(n);
	if n=2 then 
		m[1][2]:=0; m[2][1]:=0; 
	else
		for i in [1..n-1] do m[i][i+1]:=3; m[i+1][i]:=3; od;
		m[1][n]:=3; m[n][1]:=3;
	fi;
	return m;
end;

CoxeterMatrixAffineBn_:=function(n)
	local m,i;
	if not IsInt(n) or n<4 then return fail; fi;
	m:=NullMat(n,n)+2-IdentityMat(n);
	for i in [1..n-3] do m[i][i+1]:=3; m[i+1][i]:=3; od;
	m[n-2][n-1]:=4; m[n-1][n-2]:=4;
	m[n][2]:=3; m[2][n]:=3;
	return m;
end;

CoxeterMatrixAffineCn_:=function(n)
	local m,i;
	if not IsInt(n) or n<3 then return fail; fi;
	m:=NullMat(n,n)+2-IdentityMat(n);
	for i in [1..n-3] do m[i][i+1]:=3; m[i+1][i]:=3; od;
	m[n-2][n-1]:=4; m[n-1][n-2]:=4;
	m[n][1]:=4; m[1][n]:=4;
	return m;
end;

CoxeterMatrixAffineDn_:=function(n)
	local m,i;
	if not IsInt(n) or n<5 then return fail; fi;
	m:=NullMat(n,n)+2-IdentityMat(n);
	for i in [1..n-3] do m[i][i+1]:=3; m[i+1][i]:=3; od;
	m[n-3][n-1]:=3; m[n-1][n-3]:=3;
	m[n][2]:=3; m[2][n]:=3;	
	return m;
end;

CoxeterMatrixAffineEn_:=function(n) # Bourbaki's numeration of vertices (branch at 4)
	local m,i;
	if not n in [7,8,9] then return fail; fi;
	m:=NullMat(n,n)+2-IdentityMat(n);	
	for i in [3..n-2] do m[i][i+1]:=3; m[i+1][i]:=3; od;
	m[1][3]:=3; m[3][1]:=3; 
	m[2][4]:=3; m[4][2]:=3;
	if n=7 then m[7][2]:=3; m[2][7]:=3; fi;
	if n=8 then m[8][1]:=3; m[1][8]:=3; fi;
	if n=9 then m[8][9]:=3; m[9][8]:=3; fi;
	return m;
end;

CoxeterMatrixAffineFn_:=function(n) 
	local m,i;
	if not n=5 then return fail; fi;
	m:=NullMat(n,n)+2-IdentityMat(n);	
	for i in [1..n-1] do m[i][i+1]:=3; m[i+1][i]:=3; od;
	m[2][3]:=4; m[3][2]:=4;	
	return m;
end;

CoxeterMatrixAffineI1m_:=function(a) 
	local m;
	if a<>0 then return fail; fi;
	m:=[[1,a],[a,1]];
	return m;
end;

CoxeterMatrixAffineGn_:=function(n) 
	local m;
	if not n=3 then return fail; fi;
	m:=[[1,6,2],[6,1,3],[2,3,1]];
	return m;
end;

CoxeterMatrixLannerZn:=function(n)
	local m;
	if not n in [4,5] then return fail; fi;
	m:=CoxeterMatrixDn(n);
	m[1][2]:=5; m[2][1]:=5;
	return m;
end;


CoxeterMatrixDynkinPath:=function(lst)
	local i,j,m,n;
	n:=Size(lst)+1;
	m:=NullMat(n,n)+2-IdentityMat(n);
	for i in [1..n-1] do
		m[i][i+1]:=lst[i]; m[i+1][i]:=lst[i];
	od;
	return m;
end;

CoxeterMatrixDynkinCycle:=function(lst)
	local i,j,m,n;
	n:=Size(lst);
	m:=NullMat(n,n)+2-IdentityMat(n);
	for i in [1..n-1] do
		m[i][i+1]:=lst[i]; m[i+1][i]:=lst[i];
	od;
	m[n][1]:=lst[n]; m[1][n]:=lst[n];
	return m;
end;

# input: list of edges like [[1,2],[3,2],[2,4]] etc.
# output: Coxeter matrix corresponding to the right-angled Coxeter group with these edges of the defining graph
CoxeterMatrixRAListOfEdges:=function(edges)
	local m,i,j,n,x,n0,v;

	n:=Maximum(Flat(edges));
	n0:=Minimum(Flat(edges));
	v:=n-n0+1;
	m:=NullMat(v,v)+IdentityMat(v);
	for x in edges do
		m[x[1]-n0+1][x[2]-n0+1]:=2; m[x[2]-n0+1][x[1]-n0+1]:=2;	
	od;
	return m;
end;



# returns the Coxeter matrix for the RACG from Figure 5.1 of Dani-Thomas' article
DaniThomasGamma:=function(d)
	local edges,i,j,x,m;	
	
	edges:=[];
	# a0=1, b0=2, b1=3, a1,a2,...,ad=4,...3+d; b2=3+d+1, b3=3+d+2,..., bd=3+d+d-1
	for i in [0..d] do Add(edges,[1,3+i]); Add(edges,[2,3+i]); od;
	Add(edges,[3,d+4]); Add(edges,[4,d+4]);
	for i in [3..d] do Add(edges,[d+2+i,d+1+i]); Add(edges,[d+2+i,i+2]); od;
	m:=CoxeterMatrixRAListOfEdges(edges);
	return m;
end;


mEx4:=CoxeterMatrixDynkinCycle([3,3,3,3,5,3,3,3,3]);
mEx4[1][8]:=3;mEx4[8][1]:=3;
mEx4[1][3]:=3;mEx4[3][1]:=3;
mEx4[2][4]:=3;mEx4[4][2]:=3;
mEx4[7][9]:=3;mEx4[9][7]:=3;

mEx9:=CoxeterMatrixDynkinPath([4,4,4,4,4,4,4]);
mEx10a:=CoxeterMatrixDynkinCycle([3,3,3,3,3,3,3,3,3]);
mEx10b:=CoxeterMatrixDynkinCycle([4,3,3,4,4,4,3,3,4]);
mEx10c:=CoxeterMatrixDynkinCycle([3,4,4,3,3,3,4,4,3]);
mEx10d:=CoxeterMatrixDynkinCycle([4,3,4,4,3,4,4,3,4]);

mEx11:=NullMat(13,13)+2-IdentityMat(13);
mEx11[1][2]:=3;mEx11[2][1]:=3;
mEx11[3][2]:=3;mEx11[2][3]:=3;
mEx11[3][4]:=4;mEx11[4][3]:=4;
mEx11[5][4]:=3;mEx11[4][5]:=3;
mEx11[5][6]:=3;mEx11[6][5]:=3;
mEx11[7][6]:=4;mEx11[6][7]:=4;
mEx11[7][8]:=4;mEx11[8][7]:=4;
mEx11[1][8]:=3;mEx11[8][1]:=3;
mEx11[3][9]:=4;mEx11[9][3]:=4;
mEx11[3][12]:=3;mEx11[12][3]:=3;
mEx11[3][13]:=3;mEx11[13][3]:=3;
mEx11[4][11]:=3;mEx11[11][4]:=3;
mEx11[7][11]:=3;mEx11[11][7]:=3;
mEx11[7][13]:=3;mEx11[13][7]:=3;
mEx11[8][10]:=3;mEx11[10][8]:=3;
mEx11[8][12]:=3;mEx11[12][8]:=3;
mEx11[9][10]:=4;mEx11[10][9]:=4;

DaniThomasFig41:=CoxeterMatrixRAListOfEdges(
	[ [1,2],[1,4],[2,3],[2,5],[3,4],[3,6],[3,12],[4,5],[4,7],[5,6],[5,8],[6,7],[6,9],[7,8],[7,10],
		[8,9],[8,11],[9,10],[9,12],[10,11],[11,12] ] );

DaniThomasFig422:=CoxeterMatrixRAListOfEdges( 
	[ [1,2],[1,5],[1,9],[2,3],[2,6],[3,4],[3,5],[3,7],[4,6],[4,8],[4,9],[5,6],[6,7],[7,8] ] );

DaniThomasFig423:=CoxeterMatrixRAListOfEdges( 
	 [[1,4],[1,5],[1,7],[2,5],[2,6],[2,7],[3,4],[3,6],[3,7]] );

LevcovitzFig4:=CoxeterMatrixRAListOfEdges( [[1,2],[1,3],[1,4],[2,5],[2,6],[2,7],[2,10],[3,5],[3,6],[3,7],[3,10],
	[4,8],[4,10],[5,6],[5,8],[6,8],[7,9],[8,9]] );

LevcovitzFig5:=CoxeterMatrixRAListOfEdges([[1,2],[1,4],[1,5],[2,3],[2,7],[3,4],[3,5],
	[4,7],[5,6],[5,8],[6,7],[7,8]]);


# example from Gert Heckmann paper, on p.113, first
Heckmann1131:=function()
	local m,n,i,j,k,x,m1,m2,m3,m4;
	n:=18;

	m1:=CoxeterMatrixAn(7);
	m2:=StructuralCopy(m1);
	m1[3][4]:=4;m1[4][3]:=4;m1[4][5]:=4;m1[5][4]:=4;
	m3:=CoxeterMatrixAn(2);
	m4:=StructuralCopy(m3);
	m:=JoinOfCoxeterMatrices([m1,m2,m3,m4]);
	m[1][15]:=3;m[15][1]:=3; m[8][15]:=3;m[15][8]:=3;
	m[7][17]:=3;m[17][7]:=3; m[14][17]:=3;m[17][14]:=3;

	return m;
end;

# example from Gert Heckmann paper, on p.113, second
Heckmann1132:=function()
	local m,n,i,j,k,x,m1,m2,m3,m4;
	n:=19;

	m1:=CoxeterMatrixAn(17);
	m2:=CoxeterMatrixAn(1);
	m3:=StructuralCopy(m2);
	m:=JoinOfCoxeterMatrices([m1,m2,m3]);
	m[3][18]:=3;m[18][3]:=3; m[15][19]:=3;m[19][15]:=3;

	return m;
end;


# returns the list of all irreducible spherical systems of rank n, n>2
AllIrreducibleSphericalSystems:=function(n)
	local S,L,i;

	if n<3 then return fail; fi;

	L:=[];
	Add(L,CoxeterMatrixAn(n));
	Add(L,CoxeterMatrixBn(n));	
	Add(L,CoxeterMatrixDn(n));

	if n=3 then Add(L,CoxeterMatrixHn(n)); fi;

	if n=4 then 
		Add(L,CoxeterMatrixHn(n));
		Add(L,CoxeterMatrixFn(n));
	fi;

	if n in [6,7,8] then Add(L,CoxeterMatrixEn(n)); fi;

	return L;
end;




# Produces a random spherical Coxeter system
# input: n = rank of the system
# output: list of irreducible spherical Coxeter matrices, whose ranks sum up to n
# First, it generates a random partition p of number n
# Then for each k in p it picks randomly an irreducible spherical system of rank k
# For k=2 we use system I2(m) with m randomly chosen between [3..n*(RootInt(n)+1)] (as a possible choice)
GenerateRandomSphericalCoxeterSystem:=function(n)
	local p,k,x,P,L,C;

	P:=Partitions(n);	
	p:=Random(P);

	L:=[];
	for k in p do
		if k=1 then Add(L,CoxeterMatrixAn(1)); continue; fi;
		if k=2 then Add(L,CoxeterMatrixI2m(Random([3..n*(RootInt(n)+1)]))); continue; fi;
		# now k>=3
		C:=AllIrreducibleSphericalSystems(k);
		Add(L,Random(C));		
	od;
	return L;
end;


# to be applied to an irreducible Coxeter matrix
# logic adapted from HAP's function "ComponentIsSpherical" by Graham Ellis
# mode=0 returns true/false; mode=1 returns [true/false,"name"];
IsSphericalComponent:=function(m,mode)
	local i,j,k,n,x,y,z,s,t,deg,lst,flag,name,degrees,largedegrees,leaves,labels,largelabels;

	flag:=false;
	name:="";
	n:=Size(m);

	repeat
		if n=1 then flag:=true; name:="A1"; break; fi;
		if n=2 then
			if m[1][2]<>0 then 
				flag:=true; 
				if m[1][2]=3 then 
					name:="A2"; 
				elif m[1][2]=4 then 
					name:="B2";
				elif m[1][2]=5 then
					name:="H2";
				elif m[1][2]=6 then 
					name:="G2";
				else 
					name:=Concatenation("I2(",String(m[1][2]),")"); 
				fi;
			fi;
			break;
		fi;
		
		degrees:=List(m,x->Size(Filtered(x,y->y>2 or y=0)));	
		largedegrees:=Filtered(degrees,x->x>2);
		leaves:=Positions(degrees,1);
		labels:=[];
		for i in [1..n-1] do for j in [i+1..n] do
			if m[i][j]<>2 then Add(labels,m[i][j]); fi;
		od;od;

		largelabels:=Filtered(labels,x->x>3); # we exclude 0=infinity labels as the first case below
		
		if 		0 in labels 			# from now on all labels are finite
			or	Size(largedegrees)>1
			or	not Size(leaves) in [2,3]
			or	Size(largelabels)>1 
			or	Maximum(degrees)>3
			or 	Size(largedegrees)>0 and Size(largelabels)>0
			or	Size(largelabels)>0 and Maximum(largelabels)>5

		then 
			break; 
		fi;
		
		# From this point on we can assume that:
		# the Coxeter diagram is connected (i.e. direct-product indecomposable);
		# there are more than two vertices;
		# all labels are finite;
		# at most one vertex has degree 3
		# either two or three vertices have degree 1;
		# at most one edge label is > 3;
		# no vertex has degree > 3;
		# if there is a vertex of degree 3 then all labels are < 4;
		# no edge label is > 5.
		
		# Case An:
		if Maximum(labels)=3 and Maximum(degrees)=2 then 
			flag:=true;
			name:=Concatenation("A",String(n));
			break;
		fi;

		# Cases Bn and F4:
		if Maximum(labels)=4 and Maximum(degrees)=2 then
			for x in leaves do
				y:=PositionProperty(m[x],z->z>2);
				if m[x][y]=4 then 
					flag:=true; name:=Concatenation("B",String(n)); break;
				fi;
			od;
			if flag then break; fi;
			if n=4 then 
				flag:=true; name:="F4"; break;
			fi;
		fi;
			
		# Case H3:
		if n=3 and Maximum(labels)=5 then flag:=true; name:="H3"; break; fi;
			
		# Case H4:
		if n=4 and Maximum(labels)=5 then   # since there are no branch vertices in this case
			for x in leaves do
				y:=PositionProperty(m[x],z->z>2);
				if m[x][y]=5 then 
					flag:=true; name:="H4"; break;
				fi;
			od;
			if flag then break; fi;
		fi;

		# Cases Dn and En:
		if Maximum(degrees)=3 then	# we know by now that all labels = 3 or 2
			x:=Position(degrees,3); # x is the (only) branch vertex (i.e. of degree 3)
			lst:=Positions(m[x],3); # which vertices have label 3 on the edge from branch vertex
			deg:=degrees{lst}; # deg is the list of degrees of 3 neighbors of the branch vertex
			Sort(deg);
			if deg=[1,1,1] or deg=[1,1,2] then 
				flag:=true; 
				name:=Concatenation("D",String(n)); 
				break; 				
			fi;
			if deg=[1,2,2] then 
				if n in [6,7] then
					flag:=true;
					name:=Concatenation("E",String(n)); 
					break;
				fi;
				if n=8 then  
					# to exclude case "E7~":
					t:=[];
					for y in lst do
						if degrees[y]=1 then continue; fi;
						z:=PositionsProperty(m[y],s->s>2); RemoveSet(z,x);
						Add(t,z[1]);
					od;
					if ForAny(t,y->y in leaves) then
						flag:=true;
						name:="E8"; 
						break;
					fi;
				fi;
			fi;
		fi;

	until true;
	
	if mode=0 then return flag; else return [flag,name]; fi;	
end;


# my function for testing an arbitrary Coxeter matrix m if it is spherical (not necessarily irreducible)
# mode = 0, returns true or false; mode = 1 returns also a string of spherical types
IsSpherical0:=function(m,mode)
	local C,x,L,D,lst,res,s,flag,i;
	if m=[] then 
		flag:=true;s:="1"; 
		if mode=0 then 
			return flag; 
		else
			return [flag,s];
		fi;
	fi;
	L:=List(DirectProductDecomposition(m),x->CoxeterSubmatrix(m,x));
	res:=List(L,x->IsSphericalComponent(x,mode));
	if mode=0 then 
		return ForAll(res,x->x=true); 
	else 
		flag:=ForAll(res,x->x[1]=true);
		s:="";
		if flag then 
			for i in [1..Size(res)-1] do
				s:=Concatenation(s,res[i][2]," ");
			od;
			s:=Concatenation(s,res[Size(res)][2]);
		fi;
		return [flag,s];
	fi;
end;


# to be applied to an irreducible Coxeter matrix
IsAffineComponent:=function(m,mode)
	local i,j,k,n,x,y,z,s,t,deg,lst,flag,name,degrees,largedegrees,leaves,labels,largelabels;

	flag:=false;
	name:="";
	n:=Size(m);

	repeat
		if n=1 then break; fi;
		if n=2 then
			if m[1][2]=0 then 
				flag:=true;
				name:="A1~"; 
			fi;
			break;
		fi;
				
		degrees:=List(m,x->Size(Filtered(x,y->y>2 or y=0)));	
		largedegrees:=Filtered(degrees,x->x>2); 
		leaves:=Positions(degrees,1);
		labels:=[];
		for i in [1..n-1] do for j in [i+1..n] do
			if m[i][j]<>2 then Add(labels,m[i][j]); fi;
		od;od;

		largelabels:=Filtered(labels,x->x>3); # we exclude 0=infinity labels in the first case below
		
		if 		0 in labels 			# from now on all labels are finite
			or	Size(largedegrees)>2
			or	not Size(leaves) in [0,2,3,4]
			or	Size(largelabels)>2 
			or	Maximum(degrees)>4
			or	not IsSubset([3,4,6],AsSet(labels))

		then 
			flag:=false; break; 
		fi;
		
		# From this point on we can assume that:
		# the Coxeter diagram is connected (i.e. direct-product indecomposable);
		# there are more than two vertices;
		# all labels are finite;
		# at most two vertices have degree 3
		# either 0,2,3 or 4 vertices have degree 1;
		# no vertex has degree > 4;
		# all labels are in the set [3,4,6];

		
		# Case An~:
		if ForAll(degrees,x->x=2) and ForAll(labels,x->x=3) then
			flag:=true;
			name:=Concatenation("A",String(n-1),"~");
			break;
		fi;

		# Case Cn~:
		if Maximum(degrees)=2 and Size(leaves)=2 and Size(largelabels)=2 and Maximum(labels)=4 then
			lst:=[];		
			for x in leaves do
				y:=PositionProperty(m[x],z->z>2);
				Add(lst,m[x][y]);
			od;
			if ForAll(lst,x->x=4) then 
				flag:=true;
				name:=Concatenation("C",String(n-1),"~");
				break;
			fi;
		fi;

		# Case F4~:
		if n=5 and Maximum(degrees)=2 and Size(leaves)=2 and Size(largelabels)=1 and Maximum(labels)=4 then
			lst:=[];
			for x in leaves do
				y:=PositionProperty(m[x],z->z>2);
				Add(lst,m[x][y]);
			od;
			if not ForAny(lst,x->x=4) then
				flag:=true;
				name:="F4~";
				break;
			fi;
		fi;

		# Case G2~:
		if n=3 and Maximum(degrees)=2 and Size(leaves)=2 and Size(largelabels)=1 and Maximum(labels)=6 then
			flag:=true;
			name:="G2~";
			break;
		fi;

		# Case Bn~:
		if Size(largedegrees)=1 and Maximum(degrees)=3 and Size(largelabels)=1 and Maximum(labels)=4 and Size(leaves)=3 then
			x:=Position(degrees,3); 
			lst:=PositionsProperty(m[x],y->y>2); # neighbors of branch vertex x
			deg:=degrees{lst}; # deg is the list of degrees of 3 neighbors of the branch vertex
			Sort(deg);
			if deg=[1,1,1] and n=4 then
				flag:=true;
				name:="B3~";
				break;
			fi;
			if deg=[1,1,2] then 
				t:=List(leaves,y->PositionProperty(m[y],z->z>2)); # neighbors of leaves
				if ForAny([1,2,3],i->t[i]<>x and m[leaves[i]][t[i]]=4) then	
					flag:=true; 
					name:=Concatenation("B",String(n-1),"~");
					break; 				
				fi;
			fi;
		fi;
		
		# Case D4~:
		if n=5 and Size(largedegrees)=1 and Maximum(degrees)=4 and Maximum(labels)=3 and Size(leaves)=4 then
			flag:=true;
			name:="D4~";
			break;
		fi;
	
		# Case Dn~, n>4:
		if Size(largedegrees)=2 and Maximum(degrees)=3 and Maximum(labels)=3 then
			deg:=Positions(degrees,3);
			lst:=[];
			for x in deg do
				s:=Positions(m[x],3); # neighbors of x
				t:=degrees{s};
				Sort(t);
				Add(lst,t);
			od;
			if ForAll(lst,x->x=[1,1,2] or x=[1,1,3]) then
				flag:=true; 
				name:=Concatenation("D",String(n-1),"~");
				break; 				
			fi;
		fi;

		# Case En~, n=6,7,8:
		if (n in [7,8,9]) and Size(largedegrees)=1 and Maximum(degrees)=3 and Maximum(labels)=3 then
			x:=Position(degrees,3);			
			lst:=Positions(m[x],3); # neighbors of branch vertex x
			deg:=degrees{lst}; # deg is the list of degrees of 3 neighbors of the branch vertex
			Sort(deg);
			if deg=[2,2,2] and n=7 then 
				flag:=true; 
				name:="E6~";
				break; 				
			fi;
			if deg=[1,2,2] then
				t:=[];
				for y in lst do
					if degrees[y]=1 then continue; fi;
					z:=PositionsProperty(m[y],s->s>2); RemoveSet(z,x);
					Add(t,z[1]);
				od;
				if ForAny(t,y->y in leaves) and n=9 then
					flag:=true;
					name:="E8~"; 
					break;
				fi;
				if not ForAny(t,y->y in leaves) and n=8 then
					flag:=true;
					name:="E7~"; 
					break;
				fi;
			fi;
		fi;		

	until true;

	if mode=0 then return flag; else return [flag,name]; fi;
end;


# a slightly inefficient procedure; it is better to use "IsAffineComponent(m)" or "IsLannerComponent(m)"
# (see below)
IsMinimalNonsphericalComponent:=function(m)
	local ML,s,flag,i,mns,k,M;

	mns:=false;	
	if not IsSphericalComponent(m,0) then
		k:=Size(m); flag:=true;
		for i in [1..k] do
			s:=[1..k]; RemoveSet(s,i);
			M:=CoxeterSubmatrix(m,s);
			if not IsSpherical0(M,0) then
				flag:=false; break;
			fi;
		od;
		if flag then mns:=true; fi;
	fi;			
	return mns;
end;

# checks if m is the Coxeter matrix of one of the Lanner's hyperbolic systems (see Table 6.2 of Davis' book)
IsLannerComponent:=function(m)
	local i,j,k,n,x,y,z,s,t,deg,lst,lst2,flag,name,degrees,largedegrees,leaves,labels,largelabels;

	flag:=false;
	n:=Size(m);

	repeat

		if not n in [3,4,5] then break; fi;
				
		degrees:=List(m,x->Size(Filtered(x,y->y>2 or y=0)));	
		largedegrees:=Filtered(degrees,x->x>2); 
		leaves:=Positions(degrees,1);
		labels:=[];
		for i in [1..n-1] do for j in [i+1..n] do
			if m[i][j]<>2 then Add(labels,m[i][j]); fi;
		od;od;

		largelabels:=Filtered(labels,x->x>3); # we exclude 0=infinity labels in the first case below
		Sort(largelabels);

		if 0 in labels then break; fi;

		if n=3 then 
			s:=1/m[1][2]+1/m[1][3]+1/m[2][3];
			if s<1 then flag:=true; fi;
			break;
		fi;
		
		# from now on n=4 or 5

		if 		Size(largedegrees)>2
			or	not Size(leaves) in [0,2,3]
			or	Size(largelabels)>2 
			or	Maximum(degrees)>3
			or	not IsSubset([3,4,5],AsSet(labels))

		then 
			break; 
		fi;

		# ending labels
		lst:=[];
		for x in leaves do
			y:=PositionProperty(m[x],z->z>2);
			Add(lst,m[x][y]);
		od;

		# case of simple path
		if Maximum(degrees)=2 and Size(leaves)=2 then

			if largelabels=[5] then
				
				# o---o-(5)-o---o	
				if n=4 and ForAll(lst,x->x=3) then
					flag:=true; break;
				fi;

				# o-(5)-o---o---o---o
				if n=5 and ForAny(lst,x->x=5) then
					flag:=true; break;
				fi;
			fi;
			
			if largelabels=[5,5] then
				# o-(5)-o---o-(5)-o   or   o-(5)-o---o---o-(5)-o
				if ForAll(lst,x->x=5) then
					flag:=true; break;
				fi;
			fi;

			if largelabels=[4,5] then
				# o-(5)-o---o-(4)-o   or   o-(5)-o---o---o-(4)-o
				if AsSet(lst)=[4,5] then
					flag:=true; break;
				fi;
			fi;

		fi;

		# case of Z4, Z5 (one branching point)
		if largedegrees=[3] and Size(leaves)=3 and largelabels=[5] then
			if ForAny(lst,x->x=5) then
				if n=4 then flag:=true; break; fi;
				# n=5
				x:=Position(degrees,3); 
				lst2:=Filtered(m[x],y->y>2); # labels at branch vertex x
				if ForAll(lst2,y->y=3) then
					flag:=true; break;
				fi;
			fi;
		fi;


		# case of cycle
		if ForAll(degrees,x->x=2) then

			# (4,3,3,3) or (4,3,3,3,3)
			if largelabels=[4] then flag:=true; break; fi;

			# (5,3,3,3)
			if largelabels=[5] and n=4 then flag:=true; break; fi;

			# (4,3,4,3) or (4,3,5,3) or (5,3,5,3)
			if n=4 and largelabels in [[4,4],[4,5],[5,5]] then       # largelabels is sorted already
				if ForAll(m,x->Size(Filtered(x,y->y>3))=1) then
					flag:=true; break;
				fi;		
			fi;
		fi;

	until true;
	return flag;
end;



IsOneEnded:=function(m)
	local C,i,j,x,s,iter,n,flag,mc,S,mS,c;

	n:=Size(m);
	iter:=IteratorOfCombinations([1..n]);	
	flag:=true;
	for c in iter do
		mc:=CoxeterSubmatrix(m,c);
		if IsSpherical0(mc,0) then
			S:=Difference([1..n],c);
			mS:=CoxeterSubmatrix(m,S);
			C:=ConnComponents(mS,0);
			if Size(Collected(C))>1 then 
				flag:=false;
				break;
			fi;
		fi;				
	od;
	return flag;
end;


NrEnds:=function(m)
	local C,i,j,x,s,iter,n,flag,mc,S,mS,c,sz,lst,lst2,L;

	if IsSpherical0(m,0) then return 0; fi;

	lst:=DirectProductDecomposition(m);
	L:=List(lst,x->CoxeterSubmatrix(m,x));
	lst2:=Positions(L,IdentityMat(2)); # A1~ subsystems
	if Size(lst2)=1 then
		if ForAll(L{Difference([1..Size(L)],lst2)},x->IsSphericalComponent(x,0)) then
			return 2; # i.e. all components except a single A1~ are spherical
		fi;
	fi;

	n:=Size(m);
	iter:=IteratorOfCombinations([1..n]);	
	flag:=true;
	for c in iter do
		mc:=CoxeterSubmatrix(m,c);
		if IsSpherical0(mc,0) then
			S:=Difference([1..n],c);
			mS:=CoxeterSubmatrix(m,S);
			C:=ConnComponents(mS,0);
			sz:=Size(Collected(C));
			if sz>1 then
				return infinity;
			fi;
		fi;				
	od;
	return 1;
end;






# 
# creates a dictionary of subsets of [1..n] for n=Size(m), with fields: 
# [ConnComponents, IsSpherical, IsAffine, IsMinimalNonspherical, CentralizerSubsystem]
#
ProcessSpecialSubsystems:=function(m)
	local d,i,j,x,s,iter,n,c,C,lst,res,U,L,ML,M,y,sph,aff,mns,k,flag;

	n:=Size(m);
	d:=NewDictionary([1..n],true);
	iter:=IteratorOfCombinations([1..n]);
	AddDictionary(d,[],[[],true,false,false,[1..n]]);
	for c in iter do
		if c=[] then continue; fi;

		lst:=[];
		M:=CoxeterSubmatrix(m,c);

		# connected components
		C:=ConnComponents(M,2); # 2 encodes disconnectedness of vertices in the Dynkin diagram
		U:=Unique(C);
		L:=List(U,i->Positions(C,i));	
		Add(lst,List(L,x->c{x}));

		ML:=List(L,x->CoxeterSubmatrix(M,x));

		# is it spherical?
		res:=List(ML,x->IsSphericalComponent(x,0));
		sph:=ForAll(res,x->x=true);
		Add(lst,sph);

		# is it affine?
		aff:=false;
		if Size(ML)=1 then 
			if IsAffineComponent(ML[1],0) then aff:=true; fi;
		fi;
		Add(lst,aff);

		# is it minimal nonspherical?
		if Size(ML)<>1 then 
			mns:=false;
		else
			mns:=IsMinimalNonsphericalComponent(ML[1]);
		fi;
		Add(lst,mns);

		# centralizer
		s:=[];
		for x in c do
			Add(s,Positions(m[x],2));
		od;
		Add(lst,Intersection(s));
		
		AddDictionary(d,c,lst);
	od;
	return d;
end;



# takes a list of maximal (via inclusion) sets L and a set s; 
# returns an updated list, where s is incorporated:
# if s<=t for some t in L, nothing is changed
# if s>t for some t in L, s is added and all such t are eliminated
# if s is incomparable with all t in L, s is just added to the resulting list
update_maximals:=function(L,s)
	local i,x,t,T,newelt;
	T:=ShallowCopy(L);
	for t in T do 
		if IsSubset(t,s) then return; fi;
		if IsSubset(s,t) then RemoveSet(L,t); fi;
	od;
	AddSet(L,AsSet(s));
	return;
end;



# computes the equivalence relation components for hypergraph index
# input: ambient Coxeter matrix M, list of subsets of vertices L
# output: the list of colors corresponding to equivalence classes of subsets
ConnComponentsSubsets:=function(M,L)
	local C,c,n,i,j,k,m,c0;
	
	n:=Size(L); # number of subsets in L
	C:=List([1..n],i->0); # initializing the list of colors, 0 means unvisited subset
	m:=0; # m is the number of colors involved so far

	for i in [1..n] do
		# looping over subsets and checking intersections
		
		if C[i]=0 then m:=m+1; C[i]:=m; fi; # a new color for an unvisited subset
		
		c:=C[i]; # the color of the current subset
		
		for j in [i+1..n] do
			if not IsSpherical0(CoxeterSubmatrix(M,Intersection(L[i],L[j])),0) then  # if subsets i and j have infinite intersection
				if C[j]=c then continue; fi; # j-th vertex already has same color as i-th, do nothing
				if C[j]=0 then C[j]:=c; continue; fi; # if j-th vertex is unvisited, paint it in the color of i-th vertex
				
				# now C[j] is different from c and non-zero
				
				# if j-th vertex color is bigger than the i-th one, 
				# we repaint the whole component of j-th vertex into i-th color
				if C[j]>c then
					c0:=C[j];
					for k in [1..n] do 
						if C[k]=c0 then C[k]:=c; fi;
					od;
					continue;
				fi;
					
				# now C[j]<c and we need to repaint the whole component of i-th vertex
				# into the color of j-th vertex
				c0:=C[j];
				for k in [1..n] do
					if C[k]=c then C[k]:=c0; fi;
				od;
				c:=c0;  # now the current color is c0
			fi;
		od;
	od;
	return C;
end;

INFOLEVEL:=0;

# input: Coxeter matrix m
# output: [h,L]; h is the hypergraph index, L is a list of subsets [Lambda_0,Lambda_1,...,Lambda_h]
HypergraphIndex:=function(m)
	local d,i,j,x,n,C,s,h,L,isRA,Lambda0,iter,c,M,U,lst,
		comp,isSph,cc,cent,Res,CC,len,len2,mm,Om,c1,n1,iter1,maxsph,isAff;

	n:=Size(m);
		
	Lambda0:=[];Om:=[];

	# iterating through subsystems of m, forming sets Omega and Psi for hypergraph index
	iter:=IteratorOfCombinations([1..n]);
	for c in iter do
		if c=[] then continue; fi;

		M:=CoxeterSubmatrix(m,c);

		# connected components
		C:=ConnComponents(M,2); # 2 encodes disconnectedness of vertices in the Dynkin diagram
		U:=Unique(C);
		L:=List(U,i->Positions(C,i));	
		comp:=List(L,x->c{x}); # components of subsystem c
		
		isSph:=true;
		for cc in comp do
			mm:=CoxeterSubmatrix(m,cc);
			if not IsSphericalComponent(mm,0) then
				isSph:=false;
				break;
			fi;
		od;
		
		if not isSph then
			s:=[];
			for i in c do
				Add(s,Positions(m[i],2)); # centralizer of vertex i of c
			od;
			cent:=Difference(Intersection(s),c); # max commuting subsystem with c
			if INFOLEVEL>0 then 
				Print("subsystem: ",comp,", centralizer: ",cent,"\n");
			fi;
			
			# adding direct product of infinite subsystems (Omega part)
			if not IsSpherical0(CoxeterSubmatrix(m,cent),0) then
				update_maximals(Lambda0,Union(cent,c));
				Add(Om,Union(cent,c)); 
				if INFOLEVEL>0 then 
					Print("   infinites:",c," ",cent,"\n");
				fi;
			fi;

			# adding affine of rank >2 times finite (or trivial)
			isAff:=false; # by default is not affine of rank >2
			if Size(comp)=1 then
				if IsAffineComponent(CoxeterSubmatrix(m,comp[1]),0) then isAff:=true; fi;
				if isAff and Size(comp[1])>2 then  # to exclude A1~
					update_maximals(Lambda0,comp[1]);
					Add(Om,comp[1]); 
					if INFOLEVEL>0 then 
						Print("   affine:",comp[1],"\n");
					fi;

					# maximal spherical subsystems of centralizer cent
					maxsph:=[]; n1:=Size(cent);
					if n1>0 then
						iter1:=IteratorOfCombinations([1..n1]);
						for c1 in iter1 do
							if c1=[] then continue; fi;
							x:=cent{c1};
							if IsSpherical0(CoxeterSubmatrix(m,x),0) then
								update_maximals(maxsph,x);
							fi;
						od;
						for x in maxsph do
							update_maximals(Lambda0,Union(x,comp[1]));
							Add(Om,Union(x,comp[1]));
							if INFOLEVEL>0 then 
								Print("   (affine)x(finite):",comp[1]," ",x,"\n");
							fi;
						od;
					fi;
				fi;
			fi;			

			# adding cones over minimal non-spherical subsystem (Psi part), excluding affine of rk>2 treated before
			if Size(comp)=1 then
				#if IsMinimalNonsphericalComponent(CoxeterSubmatrix(m,comp[1])) then
				if (isAff and Size(comp[1])=2) or IsLannerComponent(CoxeterSubmatrix(m,comp[1])) then
					for i in [1..n] do
						if i in comp[1] then continue; fi;
						if ForAll(comp[1],x->m[i][x]=2) then
							update_maximals(Lambda0,Union(comp[1],[i]));
							if INFOLEVEL>0 then 
								Print("   (minimal inf)x(s):",comp[1]," ",[i],"\n");
							fi;
						fi;
					od;
				fi;
			fi;
		fi;
	od;	
	
	if INFOLEVEL>0 then 
		Print("Omega = ",Om,"\n","L0 = ",Lambda0,"\n");
	fi;

	if Om=[] then return [infinity,Lambda0]; fi;

	L:=Lambda0;Res:=[L];

	# iterating hyperedges
	len:=List(Lambda0,Size);
	len2:=[];
	while not (n in len) and len<>len2 do
		CC:=ConnComponentsSubsets(m,L);
		U:=Unique(CC);
		lst:=List(U,i->Positions(CC,i));	
		L:=List(lst,x->Union(L{x}));
		len2:=len;
		len:=List(L,Size);
		if len<>len2 then Add(Res,L); fi;
	od;

	if n in len then h:=Size(Res)-1; else h:=infinity; fi;
	return [h,Res];
end;

# An enhanced version (hopefully)
# input: Coxeter matrix m
# output: [h,L]; h is the hypergraph index, L is a list of subsets [Lambda_0,Lambda_1,...,Lambda_h]
HypergraphIndex_:=function(m)
	local d,i,j,x,y,n,C,s,h,L,isRA,Lambda0,iter,c,M,U,lst,
		comp,isSph,cc,cent,Res,CC,len,len2,mm,Om,c1,n1,iter1,maxsph,isAff;

	n:=Size(m);
		
	Lambda0:=[];Om:=[];

	# iterating through subsystems of m, forming sets Omega and Psi for hypergraph index
	iter:=IteratorOfCombinations([1..n]);
	for c in iter do
		if c=[] then continue; fi;

		M:=CoxeterSubmatrix(m,c);

		# connected components
		C:=ConnComponents(M,2); # 2 encodes disconnectedness of vertices in the Dynkin diagram
		#U:=Unique(C);
		U:=List(Collected(C),x->x[1]);
		L:=List(U,i->Positions(C,i));	
		comp:=List(L,x->c{x}); # components of subsystem c
		
		isSph:=true;
		for cc in comp do
			mm:=CoxeterSubmatrix(m,cc);
			if not IsSphericalComponent(mm,0) then
				isSph:=false;
				break;
			fi;
		od;
		
		if not isSph then
			s:=[];
			for i in c do
				Add(s,Positions(m[i],2)); # centralizer of vertex i of c
			od;
			cent:=Difference(Intersection(s),c); # max commuting subsystem with c
			if INFOLEVEL>0 then 
				Print("subsystem: ",comp,", centralizer: ",cent,"\n");
			fi;
			
			# adding direct product of infinite subsystems (Omega part)
			if not IsSpherical0(CoxeterSubmatrix(m,cent),0) then
				update_maximals(Lambda0,Union(cent,c));
				Add(Om,Union(cent,c)); 
				if INFOLEVEL>0 then 
					Print("   infinites:",c," ",cent,"\n");
				fi;
			fi;

			# adding affine of rank >2 times finite (or trivial)
			isAff:=false; # by default is not affine of rank >2
			if Size(comp)=1 then
				if IsAffineComponent(CoxeterSubmatrix(m,comp[1]),0) then isAff:=true; fi;
				if isAff and Size(comp[1])>2 then  # to exclude A1~
					update_maximals(Lambda0,comp[1]);
					Add(Om,comp[1]); 
					if INFOLEVEL>0 then 
						Print("   affine:",comp[1],"\n");
					fi;

					# maximal spherical subsystems of centralizer cent
					maxsph:=[]; n1:=Size(cent);
					if n1>0 then
						iter1:=IteratorOfCombinations([1..n1]);
						for c1 in iter1 do
							if c1=[] then continue; fi;
							x:=cent{c1};
							if IsSpherical0(CoxeterSubmatrix(m,x),0) then
								update_maximals(maxsph,x);
							fi;
						od;
						for x in maxsph do
							y:=Union(x,comp[1]);
							update_maximals(Lambda0,y);
							Add(Om,y);
							if INFOLEVEL>0 then 
								Print("   (affine)x(finite):",comp[1]," ",x,"\n");
							fi;
						od;
					fi;
				fi;
			fi;			

			# adding cones over minimal non-spherical subsystem (Psi part), excluding affine of rk>2 treated before
			if Size(comp)=1 then
				if (isAff and Size(comp[1])=2) or IsLannerComponent(CoxeterSubmatrix(m,comp[1])) then
					for i in [1..n] do
						if i in comp[1] then continue; fi;
						if ForAll(comp[1],x->m[i][x]=2) then
							update_maximals(Lambda0,Union(comp[1],[i]));
							if INFOLEVEL>0 then 
								Print("   (minimal inf)x(s):",comp[1]," ",[i],"\n");
							fi;
						fi;
					od;
				fi;
			fi;
		fi;
	od;	
	
	if INFOLEVEL>0 then 
		Print("Omega = ",Om,"\n","L0 = ",Lambda0,"\n");
	fi;

	if Om=[] then return [infinity,Lambda0]; fi;

	L:=Lambda0;Res:=[L];

	# iterating hyperedges
	len:=List(Lambda0,Size);
	len2:=[];
	while not (n in len) and len<>len2 do
		CC:=ConnComponentsSubsets(m,L);
		#U:=Unique(CC);
		U:=List(Collected(CC),x->x[1]);
		lst:=List(U,i->Positions(CC,i));	
		L:=List(lst,x->Union(L{x}));
		len2:=len;
		len:=List(L,Size);
		if len<>len2 then Add(Res,L); fi;
	od;

	if n in len then h:=Size(Res)-1; else h:=infinity; fi;
	return [h,Res];
end;



# Performs the duplex construction on a RACG represented by Coxeter matrix m, by making every vertex into a pair 
# of vertices connected by the edge labeled 'a'. If u,v of RACG were connected (i.e. commuting), the new pairs 
# of vertices are commuting (setwise) too. If u,v were joined by infinity label, the new pairs of vertices form 
# a join with labels 'b'. E.g. a=2, b=7. 
DuplexRACG:=function(m,a,b)
	local i,j,k,M,x,n;

	if not ForAll(Flat(m),x->x in [0,1,2]) then return fail; fi;

	n:=Size(m);
	M:=NullMat(2*n,2*n) + IdentityMat(2*n);

	for i in [1..n] do for j in [i..n] do
		if i=j then 
			M[2*i][2*i-1]:=a; M[2*i-1][2*i]:=a; 
			continue; 
		fi; 		
		if m[i][j]=2 then
			M[2*i][2*j]:=2;     M[2*j][2*i]:=2;
			M[2*i][2*j-1]:=2;   M[2*j-1][2*i]:=2;
			M[2*i-1][2*j]:=2;   M[2*j][2*i-1]:=2;
			M[2*i-1][2*j-1]:=2; M[2*j-1][2*i-1]:=2;
			continue;
		fi;
		if m[i][j]=0 then
			M[2*i][2*j]:=b;     M[2*j][2*i]:=b;
			M[2*i][2*j-1]:=b;   M[2*j-1][2*i]:=b;
			M[2*i-1][2*j]:=b;   M[2*j][2*i-1]:=b;
			M[2*i-1][2*j-1]:=b; M[2*j-1][2*i-1]:=b;
			continue;
		fi;
		Print("incorrect Coxeter matrix!\n");
		return fail;
	od;od;
	return M;
end;




# checks if mt is a subsystem of Coxeter system ms (both represented as Coxeter matrices)
IsSubsystem:=function(ms,mt)
	local cs,ct,i,j,x,ns,nt,flag,comb,fs,ft,lst,mc,c;

	ns:=Size(ms);
	nt:=Size(mt);
	if nt>ns then return false; fi;

	fs:=Collected(Flat(ms)); ft:=Collected(Flat(mt));
	if not IsSubset(Flat(ms),Flat(mt)) then return false; fi;
	if not ForAll(ft,x->x[2]<=fs[PositionProperty(fs,y->y[1]=x[1])][2]) then return false; fi;

	# canonical representative of mt:
	ct:=Maximum(Orbit(SymmetricGroup(nt),mt,OnMatrices));

	flag:=false;		
	comb:=Combinations([1..ns],nt);
	for c in comb do
		mc:=List(ms{c},x->x{c});		
		cs:=Maximum(Orbit(SymmetricGroup(nt),mc,OnMatrices));
		if cs=ct then flag:=true; break; fi;
	od;

	return flag;
end;

IsTriangleFreeRACG:=function(m)
	local i,j,x,y,flag,v,nei,sz;

	flag:=true;
	
	for v in m do
		nei:=PositionsProperty(v,x->x=2);
		sz:=Size(nei);
		for i in [1..sz-1] do for j in [i+1..sz] do
			if m[nei[i]][nei[j]]=2 then flag:=false; return flag; fi;
		od;od;
	od;
	return flag;
end;

# forms a canonical representative (maximal matrix in lex order) of the orbit,
# under graph isomorphisms of a RACG Coxeter matrix
MaximumSymOrbit:=function(m)
	local n,i,j,mm,x,G,iter,m1,c,sz,CHS;

	CHS:=10^7;
	
	n:=Size(m);
	G:=SymmetricGroup(n); sz:=Factorial(n);
	iter:=Iterator(G);
	mm:=ShallowCopy(m);

	c:=0;
	for x in iter do
		c:=c+1;
		if c mod CHS = 0 then Print(c/CHS," out of ",Int(sz/CHS),"\n"); fi;
		m1:=OnMatrices(m,x);
		if m1>mm then 
			mm:=ShallowCopy(m1);
		fi;		
	od;	
	
	return mm;
end;


# a much faster version of computing a canonical representative of the orbit:
# computes degrees of vertices, sorts them in descending order
# and then applies only those permutations that preserve degrees vector
CanonicalRepOrbit:=function(m)
	local degs,x,p,dc,gen,s,U,i,n,G,v,w,mm,m1,iter,c,CHS,sz,m0;

	CHS:=10^7;

	n:=Size(m);

	#degs:=List(m,x->Size(PositionsProperty(x,y->not y in [1,2]))); # sequence of degrees
	degs:=List(m,Sum); # sequence of "degrees weighted by labels", infinity counts as 0
	p:=Sortex(degs,function(v,w) return v > w; end); # descending order; Permuted(degs,p)=sorted degs
	m0:=OnMatrices(m,p);
	
	dc:=Reversed(Collected(degs));
	gen:=[];s:=0;for x in dc do Add(gen,[s+1..s+x[2]]);s:=s+x[2]; od;
	U:=Union(List(gen,x->GeneratorsOfGroup(SymmetricGroup(x))));
	#G:=Group(List(U,x->p*x/p)); 
	G:=Group(U);
	sz:=Size(G);

	iter:=Iterator(G);
	mm:=ShallowCopy(m0);

	c:=0;
	for x in iter do
		c:=c+1;
		if c mod CHS = 0 then Print(c/CHS," out of ",Int(sz/CHS),"\n"); fi;
		m1:=OnMatrices(m0,x);
		if m1>mm then 
			mm:=ShallowCopy(m1);
		fi;		
	od;	
	
	return mm;
end;


