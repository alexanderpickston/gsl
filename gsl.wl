(* ::Package:: *)

(* ::Title:: *)
(*gsl*)


(* ::Code::Initialization:: *)
(* Wolfram Language Package *)

(* Created by Alexander Pickston, adapted from code originally written by Massimiliano Proietti *)

(* alexpickston@gmail.com *)


(* ::Subsubsection:: *)
(*Package dependencies*)


(* ::Code::Initialization:: *)
(* graph styling *)
graphstyle = {
   	VertexSize -> {0.4},
   	VertexLabels -> {Placed["Name", {1/2*1.05, 1/2*1.05}]},
   	ImageSize -> {146.99479166666538, Automatic},
   	VertexStyle -> {Directive[EdgeForm[{Thick, Opacity[1],Blue}], Blue]},
   	VertexLabelStyle -> Directive[White, FontFamily -> "IBM Plex Mono", 20],
   	EdgeStyle -> Directive[Black, Thick, Opacity[1]],
   	GraphLayout -> "CircularEmbedding"
    };

(* folded Kronecker product *)
Kron := KroneckerProduct[##]&

(* basis states *)
h = {{1}, {0}};
v = {{0}, {1}};
d = 1/Sqrt[2] (h + v);
a = 1/Sqrt[2] (h - v);
r = 1/Sqrt[2] (h + I*v);
l = 1/Sqrt[2] (h - I*v);

(* Partial Trace - adapted from Mark S. Tame - http://library.wolfram.com/infocenter/MathSource/5571/ *)
SwapParts[expr_, pos1_, pos2_] := 
    
    ReplacePart[#, #, {pos1, pos2}, {pos2, pos1}] &[expr];
    TraceSystem[dm_, sys_] := 
    Block[{Qubits, TrkM, n, M, k, Permut, perm, b, c, p},
            Qubits = Reverse[Sort[sys]];(* 
            rearrange the list of qubits to be traced out *)
            TrkM = dm;

   (* For all qubits to be traced out... *)
    For[q = 1, q <= Dimensions[Qubits][[1]], q++,
        n = Log[2, (Dimensions[TrkM][[1]])]; (* 
        dimensions of original system *)
        M = TrkM;
        k = Qubits[[q]];
    
    If[k == n,(* if tracing the last system *)
        TrkM = {};
        For[p = 1, p < 2^n + 1, p = p + 2,
            TrkM = 
            Append[TrkM, 
            Take[M[[p, All]], {1, 2^n, 2}] + 
            Take[M[[p + 1, All]], {2, 2^n, 2}]];
            (* Pick row p/p+1 and take elements 1/2 through 2^n in steps of 2 - sum thoese and append to zero matrix - do for all rows *)
            ],

        For[j = 0, j < (n - k), j++,(* if not - permute accordingly *) b = {0};
        For[i = 1, i < 2^n + 1, i++,
        If[(Mod[(IntegerDigits[i - 1, 2, n][[n]] + 
            IntegerDigits[i - 1, 2, n][[n - j - 1]]), 2]) == 1 && 
            Count[b, i]  == 0, 
            Permut = {i, (FromDigits[
                SwapParts[(IntegerDigits[i - 1, 2, n]), {n}, {n - j - 1}], 2] + 1)};
                b = Append[b, (FromDigits[
                SwapParts[(IntegerDigits[i - 1, 2, n]), {n}, {n - j - 1}], 2] + 1)];
                c = Range[2^n];
                perm = 
                SwapParts[c, {i}, {(FromDigits[SwapParts[(IntegerDigits[i - 1, 2, n]), {n}, {n - j - 1}], 2] + 1)}];
                M = M[[perm, perm]];]];
        
    (* and now trace out last system *)
    TrkM = {};
    For[p = 1, p < 2^n + 1, p = p + 2,
    TrkM = Append[TrkM, 
        Take[M[[p, All]], {1, 2^n, 2}] + 
        Take[M[[p + 1, All]], {2, 2^n, 2}]];
        ]
        ]
        ];
    ];
    
    Clear[Qubits, n, M, k, Permut, perm, b, c]; 
    TrkM
    ];


(* ::Subsection:: *)
(*Begin package*)


(* ::Code::Initialization:: *)
BeginPackage["gsl`"]


(* ::Code::Initialization:: *)
CustomGraph::usage="CustomGraph[edges_] From a list of edges, create a graph using. To make a graph equivalent to a GHZ state, then edges={{1,2},{2,3}}";


(* ::Code::Initialization:: *)
LCQubit::usage="LCQubit[graph_,vertex_] Performing the local complementation operation (LC) onto a selected qubit of a graph state";


(* ::Code::Initialization:: *)
LCOrbit::usage="LCOrbit[graph_] Return the orbit from a given graph without any isometric rquivalents in the output";


(* ::Code::Initialization:: *)
Zmeasurement::usage="Zmeasurement[graph_,vertex_] Performs a Z measurement onto the vertex of a graph";
Ymeasurement::usage="Ymeasurement[graph_,vertex_] Performs a Y measurement onto the vertex of a graph";
Xmeasurement::usage="Xmeasurement[graph_,vertex_] Performs a X measurement onto the vertex of a graph, recall that this does the operation of a Y measurement on a randomly selected neighbour of the chosen vertex";


(* ::Code::Initialization:: *)
FindStabilzers::usage="FindStabilizers[state_] For a given state, return the stabilzers of the state. This works by finding which combination of operators \"stabilize\" the state. The state after applying the operation is equivalent to the state before applying the operation";


(* ::Code::Initialization:: *)
FindGraph::usage="FindGraph[stabilizers_] From a list of stabilizers, return combinations of stabilizer generators with a specific pattern: only those combinations that contain one Pauli X operator per node in the graph state.";


(* ::Code::Initialization:: *)
DrawGraph::usage="FindGraph[stabilizers_] From the results of FindGraph[] (a list of stabilizers), construct a graph based on the relationships between qubits specified by the input stabilizers";


(* ::Code::Initialization:: *)
Begin["`Private`"]


(* ::Subsection:: *)
(*Defined functions*)


(* ::Code::Initialization:: *)
Module[{input, out},
    CustomGraph[edges_] := (
    
        (* edges should be a string*)
        (* should be of the form: 
        edges={{1,2},{2,3}} *)

        input = Table[edges[[i, 1]] \[UndirectedEdge] edges[[i, 2]]
          , {i, Length@edges}];

        out = Graph[input, graphstyle];
    Return[out])
];


(* ::Code::Initialization:: *)
Module[{subGraph,diffGraph,complementGraph,out,g,vertexCoordinates},
	LCQubit[graph_,vertex_]:=(

		(* get the vertex coordinates of the original graph *)
		vertexCoordinates=GraphEmbedding[graph];

		(* apply the vertex coordinates to the original graph *)
		g=Graph[VertexList[graph],EdgeList[graph],VertexCoordinates->vertexCoordinates];

		(* select the subgraph generated by the vertex and its neighbours *)
		subGraph=Subgraph[graph,AdjacencyList[graph,vertex]];

		(* complement the sub graph *)
		complementGraph=GraphComplement[subGraph];

		(* remove the starting subgraph *)
		diffGraph=GraphDifference[graph,subGraph];

		(* union the new subGraph with the remaining main graph *)
		out=GraphUnion[diffGraph,complementGraph];
		out=Graph[out,graphstyle,VertexCoordinates->vertexCoordinates];

	(* return the LC-equivalent graph *)
	Return[out];);
];


(* ::Code::Initialization:: *)
Module[{perm,prmList,noDuplicates,g,vertexCoordinates,out},
	LCOrbit[graph_]:=(

		(* get the vertex coordinates of the original graph *)
		vertexCoordinates=GraphEmbedding[graph];

		(* apply the vertex coordinates to the original graph *)
		g=Graph[VertexList[graph],EdgeList[graph],VertexCoordinates->vertexCoordinates];

		(* module operations *)
		perm=Permutations[Range[VertexCount[graph]],VertexCount[graph]];
		prmList=FoldList[LCQubit,graph,#]&/@perm//Flatten;
		noDuplicates=DeleteDuplicates[prmList,IsomorphicGraphQ];

		(* ensure styling is correct *)
		out=Graph[noDuplicates,graphstyle,VertexCoordinates->vertexCoordinates];

	(* return the LC-equivalent graph orbit *)
	Return[noDuplicates];)
];


(* ::Code::Initialization:: *)
Module[{vertexCoordinates,g,perm,prmList,noDuplicates,out},
	LCOrbitIsomorphic[graph_]:=(

		(* get the vertex coordinates of the original graph *)
		vertexCoordinates=GraphEmbedding[graph];

		(* apply the vertex coordinates to the original graph *)
		g=Graph[VertexList[graph],EdgeList[graph],VertexCoordinates->vertexCoordinates];

		(* module operations *)
		perm=Permutations[Range[VertexCount[graph]],VertexCount[graph]];
		prmList=FoldList[LCQubit,graph,#]&/@perm//Flatten;
		noDuplicates=Select[prmList,IsomorphicGraphQ[#,graph]&];

		(* ensure styling is correct *)
		out=Graph[noDuplicates,graphstyle,VertexCoordinates->vertexCoordinates];

	(* return the LC-equivalent graph orbit *)
	Return[out];)
];


(* ::Code::Initialization:: *)
Module[{vertexCoordinates,g,edgeDelete,edgeDeleteGraph,vertexList,vertexDeleted,ordering,out},
	Zmeasurement[graph_,vertex_]:=(

		(* get the vertex coordinates of the original graph *)
		vertexCoordinates=GraphEmbedding[graph];

		(* apply the vertex coordinates to the original graph *)
		g=Graph[VertexList[graph],EdgeList[graph],graphstyle,VertexCoordinates->vertexCoordinates];

		(* module operation *)
		(* finding the complement between all edges and those edges which join to the vertex specified in the function *)
		edgeDelete=Complement[EdgeList[g],EdgeList[g,vertex\[UndirectedEdge]_]];
		edgeDeleteGraph=Graph[edgeDelete];
		vertexList=VertexList[edgeDeleteGraph];

		(* need to work out what edges have been deleted as some vertices will also be removed *)
		(* only showing vertices that still posses an edge *)
		vertexDeleted=Complement[Range@Length@vertexCoordinates,vertexList];
		(* correct re-formatting of variable to parse into the Delete[] function *)
		vertexDeleted={#}&/@vertexDeleted;
		(* new vertex co-ordinates with deleted vertices removed *) 
		vertexCoordinates=Delete[vertexCoordinates,vertex];

		(* ensure styling is correct *)
		(*out=Graph[edgeDelete,graphstyle,VertexCoordinates->vertexCoordinates];*)
		out=Graph[edgeDelete,graphstyle];

	Return[out];);
];


(* ::Code::Initialization:: *)
Module[{},
	Ymeasurement[graph_,vertex_]:=(

	(* simply return the Zmeasurement[] function applied to the LC rotated graph *)
	Return[Zmeasurement[LCQubit[graph,vertex],vertex]]);
];


(* ::Code::Initialization:: *)
Module[{randomNeighbour,tempGraph,out},
	Xmeasurement[graph_,vertex_]:=(

		(* randomly choose neighbouring vertex (where applicable) *)
		randomNeighbour=RandomChoice@AdjacencyList[graph,vertex];

		(* perform Ymeasurement[] function to said randomly chosen neighbour *)
		tempGraph=Ymeasurement[LCQubit[graph,randomNeighbour],vertex];

		(* correct styling is already applied withing the Ymeasurement[] function *)
		out=LCQubit[tempGraph,randomNeighbour];

	Return[out]);
];


(* ::Code::Initialization:: *)
Module[{dim,ops,opsList,coding,codingState,allStates,pos,out,transformations},
	FindStabilzers[state_] := (
	
		(* calculate the dimension of the quantum state *)
		dim=1/Log[Length[state],2];

		(* define a set of Pauli operators *)
		ops=Tuples[Table[{\[DoubleStruckCapitalI][i],\[DoubleStruckCapitalX][i],\[DoubleStruckCapitalZ][i],-\[DoubleStruckCapitalZ][i]},{i,1,dim}]];

		(* List of rules for the application of the Pauli matrices to basis vectors *)
		transformations={
		\[DoubleStruckCapitalI][qubit_]->{{H[qubit]->H[qubit],V[qubit]->V[qubit]}},
		\[DoubleStruckCapitalX][qubit_]->{{H[qubit]->V[qubit],V[qubit]->H[qubit]}},
		-\[DoubleStruckCapitalX][qubit_]->{{H[qubit]->-V[qubit],V[qubit]->-H[qubit]}},
		\[DoubleStruckCapitalI]*\[DoubleStruckCapitalX][qubit_]->{{H[qubit]->\[DoubleStruckCapitalI]*V[qubit],V[qubit]->\[DoubleStruckCapitalI]*H[qubit]}},
		-\[DoubleStruckCapitalI]*\[DoubleStruckCapitalX][qubit_]->{{H[qubit]->-\[DoubleStruckCapitalI]*V[qubit],V[qubit]->-\[DoubleStruckCapitalI]*H[qubit]}},
		\[DoubleStruckCapitalZ][qubit_]->{{H[qubit]->H[qubit],V[qubit]->-V[qubit]}},
		-\[DoubleStruckCapitalZ][qubit_]->{{H[qubit]->-H[qubit],V[qubit]->V[qubit]}},
		\[DoubleStruckCapitalI]*\[DoubleStruckCapitalZ][qubit_]->{{H[qubit]->\[DoubleStruckCapitalI]*H[qubit],V[qubit]->-\[DoubleStruckCapitalI]*V[qubit]}},
		-\[DoubleStruckCapitalI]*\[DoubleStruckCapitalZ][qubit_]->{{H[qubit]->\[DoubleStruckCapitalI]*H[qubit],V[qubit]->-\[DoubleStruckCapitalI]*V[qubit]}},
		\[DoubleStruckCapitalY][qubit_]->{{H[qubit]->\[DoubleStruckCapitalI]*V[qubit],V[qubit]->-\[DoubleStruckCapitalI]*H[qubit]}},
		-\[DoubleStruckCapitalY][qubit_]->{{H[qubit]->-\[DoubleStruckCapitalI]*V[qubit],V[qubit]->\[DoubleStruckCapitalI]*H[qubit]}},
		\[DoubleStruckCapitalI]*\[DoubleStruckCapitalY][qubit_]->{{H[qubit]->-V[qubit],V[qubit]->H[qubit]}},
		-\[DoubleStruckCapitalI]*\[DoubleStruckCapitalY][qubit_]->{{H[qubit]->V[qubit],V[qubit]->-H[qubit]}}};

		(* flatten the list of Pauli operators *)
		opsList=Flatten[#/.transformations]&/@ops;

		(* define a symbolic coding for the state using Kronecker product *)
		coding=Kron@@Table[{H[i],V[i]},{i,1,dim}]//Flatten;

		(* calculate the symbolic representation of the state *)
		codingState=Total[state*coding];

		(* calculate the symbolic representations of all possible states *)
		allStates=codingState/.#&/@opsList;

		(* find the positions where the state matches each possible state *)
		pos=Position[#==(codingState)&/@allStates,True]//Flatten;

		(* return the symbolic representations of the corresponding Pauli operators *)
		out=ops[[pos]];
	Return[out];)
];


(* ::Code::Initialization:: *)
Module[{dim,listStab,comb,cliffOp,combCliff,stabComb,graphGen,noSameNodeList,posStab,graphList},
	FindGraph[state_]:=(

		(* compute dimension of the input state *)
		dim=1/Log[Length[state],2];

		(* call function FindStabilzers to get a list of stabilizers from all comb of I,X,Z and -Z*)
		(* As the phase -Z does not matter for finding the graph state, remove it *)
		(* e.g. -Z,I and Z,I stabilize two different states but the same graph state *)
		(* note that the ideal routine would be to find only the stabilizer generators, still open problem *)
		listStab=Union[FindStabilzers[state]/.{-\[DoubleStruckCapitalZ][qubit_]->\[DoubleStruckCapitalZ][qubit]}];

		(* consider all combinations of Hadamard and Identity *)
		(* should be enough, but might need to consider phase gate *)
		comb=Tuples[{Table[\[DoubleStruckCapitalH][i],{i,dim}],Table[\[DoubleStruckCapitalI][i],{i,dim}]}\[Transpose]];

		(* set the replacement rules *)
		cliffOp={
		\[DoubleStruckCapitalH][qubit_]->{\[DoubleStruckCapitalI][qubit]->\[DoubleStruckCapitalI][qubit],\[DoubleStruckCapitalX][qubit]->\[DoubleStruckCapitalZ][qubit],\[DoubleStruckCapitalY][qubit]->\[DoubleStruckCapitalY][qubit],\[DoubleStruckCapitalZ][qubit]->\[DoubleStruckCapitalX][qubit]},
		\[DoubleStruckCapitalI][qubit_]->{\[DoubleStruckCapitalI][qubit]->\[DoubleStruckCapitalI][qubit],\[DoubleStruckCapitalX][qubit]->\[DoubleStruckCapitalX][qubit],\[DoubleStruckCapitalY][qubit]->\[DoubleStruckCapitalY][qubit],\[DoubleStruckCapitalZ][qubit]->\[DoubleStruckCapitalZ][qubit]}};

		(* take the first half of all the comb ;;2^(dim-1) and replace comb with a list of rules *)
		(* the second half is symmetric and will give the same results *)
		combCliff=Flatten[#]&/@(comb[[;;(2^(dim-1))]]/.cliffOp);

		(* apply the rules on the stabilizers *)
		stabComb=listStab/.combCliff;

		(* select only those with one X per group of stabilizers *)
		graphGen=Select[
		Select[#,Count[#,\[DoubleStruckCapitalX][_]]==1&]&/@stabComb,
		Length@#>=dim&];

		(* select only those with an X per node *)
		noSameNodeList=Table[
		Count[graphGen[[el]],#]&/@Table[{___,\[DoubleStruckCapitalX][i],___},{i,1,dim}],
		{el,Length@graphGen}];

		(* find their positions *)
		posStab=Position[noSameNodeList,Table[1,dim]];

		(* return the list *)
		graphList=graphGen[[#]]&/@posStab;
	Return[Flatten[graphList,1]])
];


(* ::Code::Initialization:: *)
Module[{linkList,nodeList,toGraph,noDoubleLinks,out},
	DrawGraph[stabList_]:=(

		(* construct list of vertices and edges *)
		linkList=Flatten[#]&/@(Position[#,\[DoubleStruckCapitalZ][_]]&/@stabList);
		nodeList=Flatten[(Position[#,\[DoubleStruckCapitalX][_]]&/@stabList)];

		(* pass the above list through Table[] to construct graph based on mma syntax *)
		toGraph=Table[
		nodeList[[i]]\[UndirectedEdge]#&/@linkList[[i]],
		{i,Length@nodeList}];

		(* remove cases of a repeated edge *)
		noDoubleLinks=DeleteDuplicates[Flatten[toGraph],#1==Reverse[#2]&];

		out=Graph[noDoubleLinks,graphstyle];
	Return[out])
];


(* ::Code::Initialization:: *)
End[]


(* ::Code::Initialization:: *)
EndPackage[]


(* ::Code::Initialization:: *)
chars = Characters@"gsl library has been loaded successfully. Have fun!";
list = Table[
   Style[chars[[i]], 
    Blend[{Green,Blue}, (i - 1)/(Length@chars - 1)], 
    Bold], {i, 1, Length@chars}];
Apply[Print, list]
