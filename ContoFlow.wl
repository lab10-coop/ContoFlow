(* ::Package:: *)

(* :Author: Michael Schreiber *)


(* :Version: 0.1 *)


BeginPackage["ContoFlow`"];


ContoFlowReset::usage="ContoFlowReset replaces Contos and Flows with empty associations.";


BlockTime::usage="BlockTime[t] sets block time to t. BlockTime[] returns the current block Btime.";


BlockTimePlus::usage="BlockTimePlus[] advances BlockTime t to t+1. BlockTimePlus[p] advances BlockTime to t+p.";


Contos::usage="Contos[] returns associations for all contos.";


Conto::usage="Conto[c] returns an association of keys and values for conto c. Conto[c,k] returns a value for key k.";


NewConto::usage="NewConto[] creates a new conto of default ContoType with empty balance and returns its identifier.
NewConto[i] creates a conto with string identifier i unless it exists already. 
NewConto[i,t] creates a conto with ContoType t.
NewConto[i,t,b] creates a conto with ContoType t and initial ContoBalance b.";


contyp::usage="key for contos set to 0 unless specified when creating a new one.";


ctt::usage="key for contos giving the BlockTime of contotype designation.";


bala::usage="key for contos giving the balance of a conto.";


bat::usage="key for contos giving the most recent BlockTime when ContoBalance was changed.";


ifis::usage="key for contos giving a list of ids which collects all incoming flows.";


ift::usage="key for Blocktime of most recent change of ifis.";


ofis::usage="key for contos giving a list of ids which collects all outgoing flows.";


oft::usage="key for Blocktime of most recent change of ofis.";


Pay::usage="Pay[q, s, d] moves quantity q from source conto s to destination conto d if q is less or equal to the balance of s.";


Flows::usage="Flows[] returns associations for all flows.";


Flow::usage="Flow[f] returns an association of keys and values for flow f. Flow[f,k] returns a value for key k.";


rate::usage="key for Flow giving the rate at which an accumulated quantity will change per BlockTimeStep.";


accu::usage="key for Flow giving the accumulated quantity of flows.";


NewFlow::usage="NewFlow[s, d,r] creates a Flow from source s to destination d with flowrate r per BlockTimeStep.";


Harvest::usage="Harvest[f] requests settlement of quantities accumulated by Flow f.";


Hint::usage="Hint[d] suggests settlement for destination conto d.";


Begin["`Private`"]


(* 
Reset 
*)

 ContoFlowReset[]:=CompoundExpression[bt=0; conts=<||>; flows=<||>;];
 
(* 
Block time and association spaces 
*)
 
 bt=0;
 BlockTime[]:=bt;
 BlockTime[t_]:=(bt=t);
 BlockTimePlus[]:=(bt=bt+1);
 BlockTimePlus[p_]:=(bt=bt+p);
 
 (* 
 Associations for contos and flows 
 *)
 
conts=<||>;
flows=<||>;


SetAttributes[{ato,upt},HoldFirst];
ato[as_,data_]:=AssociateTo[as,data];
upt[as_,i_String,w_,k_String,kt_String]:=(as[i,k]=w;as[i,kt]=bt;);

Contos[]:=conts;
Contos[i_,t___]:= conts[i,t];
Conto[i_,t___]:= conts[i,t];

NewConto[c_String,ct_,b_]:=newconto[c,ct,b];

(* 
conto type vertices and payment edges in block time space 
*)

csts=Flatten@{{"contyp","ctt"},{"bala","bat"},{"ifis","ift"},{"ofis","oft"}};
newconto[c_String,ct_,b_]:=If[KeyExistsQ[conts,c],{"i1",c},
ato[conts,c->AssociationThread[csts->{ct,bt,b,bt,{},bt,{},bt}]];];
 
Pay[s_String,d_String,v_]:=pay[s,d,v]; 
 
(* 
payments read and write in conto type space
*)

pay[s_String,d_String,v_]:=If[And[KeyExistsQ[conts,s],KeyExistsQ[conts,d]], 
With[{sb=conts[s,"bala"],db=conts[d,"bala"]},If[sb>=v, MapThread[(upt[conts,#1,#2,"bala","bat"];)&,{{s,d},{sb-v,db+v}}],
{"overdraft", s,d,sb,v},{"payx",s,d,sb,v}];]];

Flows[]:= flows[];
Flows[i_,t___]:= flows[i,t];
Flow[i_,t___]:= flows[i,t];

NewFlow[s_String,d_String,r_]:= newflow[s,d,r];

(* 
flow accumulation edges 
*)

fsts=Flatten@{{"accu","act"},{"rate","rat"}};
tosd[s_String,d_String]:=StringJoin[s,".",d];fromsd[sd_String]:=StringSplit[sd,"."];
newflow[s_String,d_String,r_]:=With[{sd=tosd[s,d]}, If[And[KeyExistsQ[conts,s],KeyExistsQ[conts,d],Not[KeyExistsQ[flows,sd]]],
ato[flows,sd->AssociationThread[fsts->{0,bt,r,bt}]];
MapThread[(upt[conts,#1,Append[conts[#1,#2],sd],#2,#3];)&,
{{d,s},{"ifis","ofis"},{"ift","oft"}}];,
{"i3",s,d,sd,bt}]];
(* read only in flow space *)
aatr[{a_,at_,r_}]:=a+r (-at+bt);
accf[sd_String]:=aatr[Lookup[flows[sd],{"accu","act","rate"},Return[{"acclu",sd}]]];
(* Read and write in flow rate accumulation space *)
updaccu[sd_String,v_]:=upt[flows,sd,v,"accu","act"];
updrate[sd_String,v_]:=(updaccu[sd,accf[sd]];upt[flows,sd,v,"rate","rat"];);

Harvest[sd_String]:=partial[sd];

(* 
write in both spaces 
*)

partial[sd_String]:=With[{s=First[fromsd[sd]]},With[{b=conts[s,"bala"]},
If[b>0,parti[s,b];,updaccu[sd,accf[sd]];,{"par01",sd,b,bt}];]];
parti[s_String,b_]:=With[{acs=par[s]},
With[{ta=Total[acs[[All,1]]]},
If[ta>0,With[{q=Min[b/ta,1]},
(pay[s,#[[2,2]],First[# ]*q];updaccu[Last[# ],(1-q)*First[# ]];)&/@acs],
{"par10",acs,ta,bt},{"par11",acs,ta,bt}];]];

(* read contos and flows to anticipate *)

Hint[d_String]:=hint[d,1];

par[s_String]:=({accf[#],fromsd[#],#}&/@(conts[s,"ofis"]));
balpar[s_String]:={conts[s,"bala"],Total[par[s][[All,1]]]};
compare[d_String]:={#,balpar[First@fromsd[#]]}&/@(conts[d,"ifis"]);
wvecs[d_String,\[Gamma]_]:=Sort[{If[#[[2,2]]>0,N[accf[#[[1]]]*((#[[1]]/#[[2]])&[#[[2]]]),0]]^\[Gamma],#[[1]]}&/@compare[d]];
hint[d_String,\[Gamma]_]:=If[#=={},Return[Nothing],RandomChoice[If[SameQ@@Round[First[#]],Last[#],Rule@@#]]&[Transpose[#]]]&[wvecs[d,\[Gamma]]/.Null->0];



End[];


EndPackage[]
