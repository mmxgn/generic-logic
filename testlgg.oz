declare

%% DatabaseClass
% Taken from http://www.mozart-oz.org/documentation/tutorial/node12.html

%% TODO: Tue Apr 24
%% Horn Clauses, eval() function
%% PAL

% http://lists.gforge.info.ucl.ac.be/pipermail/mozart-users/1999/000165.html
   proc {Copy X Vs0 ?Vs ?Y}
      if {IsDet X} then 
	 if {IsNumber X} then
	    Y = X
	    Vs = Vs0
	 elseif {IsRecord X} then
	    {CopyRecord X Vs0 Vs Y}
	 else
	    raise error('Copy'(X Y)) end
	 end
      else
	 {CopyVar X Vs0 Vs Y}
      end
   end
   proc {CopyRecord R Vs ?Ws ?S}
      As = {Arity R} in
      S = {MakeRecord {Label R} As}
      {CopyArgs R As Vs Ws S}
   end
   proc {CopyArgs R As Vs0 ?Vs ?S}
      case As
      of nil then Vs0 = Vs
      [] A|Ar then
	 Vs1 in
	 {Copy R.A Vs0 Vs1 S.A}
	 {CopyArgs R Ar Vs1 Vs S}
      end
   end
   proc {CopyVar X Vs Ws ?Y}
      case Vs
      of nil then Ws = [(X#Y)]
      [] (O#N)|Vr then
	 Wr in
	 if {System.eq X O} then
	    Y = N
	    Ws = Vs
	 else
	    Ws = (O#N)|Wr
	    {CopyVar X Vr Wr Y}
	 end
      end
   end
   proc {CopyTerm X Y}
      {Copy X nil _ Y}
   end


/*

declare X 
{Browse {CopyTerm f(X a  [X] X) $}}

*/   

% Switches all instances of P from list L, searches one level only.
fun {RemoveAllFromList L P}
   case L
   of nil then
      nil
   [] H|T then
      if H == P then
	 {RemoveAllFromList T P}
      else
	 H|{RemoveAllFromList T P}
      end
   else
      L
   end
end

% Removes all duplicates from L
fun {RemoveDuplicatesFromList L}
   case L
   of nil then
      nil
   []
      H|T then
      H|{RemoveDuplicatesFromList {RemoveAllFromList T H}}
   else
      L
   end
end

Z = point(x: genvar(domain: [1 2]) y: genvar(domain: [3 4]))
%{Browse Y}
{Browse Z}

P = proc {$ Label Value}
       {Browse Label#Value}
    end

{Record.forAllInd Z P}


fun {IsGenvar G}
   case G of
      genvar(domain: _) then true
   else
      false
   end
end


fun {ChoiceNet R}
    if {IsAtom R} then atom
    elseif  {IsRecord R} then record
   end
end


proc {GetGenvars L Out}
   local
      fun {GetGenvarsHelper L}
	 case L of nil then nil
	 []
	    X#Y then {GetGenvarsHelper X}|{GetGenvarsHelper Y}
	 []
	    H|T then {GetGenvarsHelper H}|{GetGenvarsHelper T}
	 []
	    X then
	    if {IsRecord X} then
	       if {Record.label X} == genvar then
		  L|{GetGenvarsHelper {Record.toList L}}
	       else
		  {GetGenvarsHelper {Record.toList L}}
	       end
	    else nil
	    end
	 end
      end


   in
      Out = {List.flatten {RemoveDuplicatesFromList {List.flatten {GetGenvarsHelper L}}}}
   end
   
end
   
{Browse {GetGenvars [genvar(3 2) genvar(3 2) genvar(a genvar(3 4)) a 1 2]}}


%{Browse {RemoveDuplicatesFromList [[1 1] 1 2 3 3 1 1 2 3 3 1 3 3 1 a(3 1) [1 1] [3 3]]}}
   
   



fun {Substitute L Orig Repl}
   % Substitutions
   %
   % Will substitute a sequence in an expression with
   % something else.
   %
   % For example:
   % {Substitute [x f(x)] x 3}
   % will return [3 f(3)]
   
   case L of
      % i.e. L = nil
      nil then nil
   []
      % i.e. if L=a#b, Orig=a, Repl=1 then return 1#b
      X#Y then {Substitute X Orig Repl}#{Substitute Y Orig Repl}
   []
      % i.e. if L=[a b]
      H|T then
 
      if L==Orig then Repl % If Orig is the same as L then replace L
      else 
	 {Substitute H Orig Repl}|{Substitute T Orig Repl} % Else search Orig in L
      end
   []
      X then % If it is something else (i.e. atom or record)
      if X==Orig then Repl
      elseif {Record.is X} then
	 {Record.mapInd L fun {$ _ A} {Substitute A Orig Repl} end} % If it is a record, search Orig in its fields.
      else L end
   else
      Orig
   end   
end


fun {Subst Expr S}
   % Same as above, but takes S in the form
   % p#q where p is what is going to be substituted
   % and q the value of the substituttion.
   case S of
      P#Q then
      {Substitute Expr P Q}
   else
      Expr
   end
end

fun {Subst2 Expr S}
   % Same as Subst2, with the exception
   % that S is a list of substitutions.
   case S of
      H|T then
      {Subst2 {Subst Expr H} T}
   []
      P#Q then
      {Substitute Expr P Q}
   else
      Expr
   end
   
end

      


{Browse {Substitute [x(3: genvar(genvar(3 2) 2)) genvar(3 2)#genvar(3 2)] genvar(3 2) 3}}
{Browse {Subst [x(3: genvar(genvar(3 2) 2)) genvar(3 2)#genvar(3 2)] genvar(3 2)#3}}
{Browse {Subst2 [u(x(one two)) [one(three four)]] [one#1 two#2 three#3 9]}}


%{Browse {SubstituteOne [genvar(domain: [3 2]) x]}}
% First, get all the generalization variables.



%% Here we provide a list and we replace every free
% variable with a tree of choicepoints.



% fun {ChoiceFromList L}
%    case L of nil then nil
%    []
%       H|T then {ChoiceFromGenvar H}|{ChoiceFromList T}
%    else
%       L
%    end
% end


%% Here we provide ChoiceFromGenvar with a generalization variable
%  and we get as a result a network of choice points for each
%  of its values.
%
%  form of a generalization variable:
%
%  genvar(domain: D) where D is a list.

fun {ChoiceFromGenvar G}
   case G of
      nil then fail
   []
      
      genvar(domain: D) then {ChoiceFromList D}
   else
      G
   end
end

% Generate a tree of choice points
% from a list L.

fun {ChoiceFromList L}
   case L
   of nil then fail
   [] H|T then
      choice {ChoiceFromGenvar H}
      [] {ChoiceFromList T} end
   else
      L
   end
end

fun {MakeChoiceNet Expr}
   case Expr
   of nil then nil
   []
      genvar(domain: D) then {ChoiceFromList D}
   []
      H|T then
      {MakeChoiceNet H}|{MakeChoiceNet T}
   []
      H#T then
      {MakeChoiceNet H}#{MakeChoiceNet T}
   []
      X then
      if {Record.is X} then
	 {Record.mapInd X fun {$ I A}
			     {MakeChoiceNet A}
			  end}
      else
	 X
      end
   else
      Expr
   end   
end


% Generate a tree of choice points from
% a list L, but for two similar genvars,
% the same choice point tree is used.

fun {ChoiceFromListP L}
   case L
   of nil then fail
   []
      genvar(domain: D) then {ChoiceFromList D}
   []
      
      H|T then
      X in
      X = {ChoiceFromListP H}
      choice X [] {ChoiceFromListP {Substitute T H X }} end
   []
      H#T then
      X in
      X = {ChoiceFromListP H}
      X#{ChoiceFromListP {Substitute T H X}} 
   []
       X then
       if {Record.is X} then
     	 {Record.mapInd X fun {$ I A}
			     {ChoiceFromListP A} end }
       else X
       end
     
   else
      L
      %{ChoiceFromListP L}
   end
end

%% Choice from genvar case

% {ExploreAll proc {$ Sol} X Y in
% 	       X = {ChoiceFromGenvar genvar(domain:[alpha beta gamma delta])}
% 	       Y = {ChoiceFromGenvar genvar(domain:[1 2 3 4])}
% 	       Sol = [X Y X]
% 	    end }

%% Choice from list case
{Browse {SearchOne proc {$ Sol} X Y Z Sol2 in
	       
	      % X = genvar(domain: [1 2 3])
	      % Y = genvar(domain: [alpha beta gamma])
	       X = x2
	       Y = y2
	       Z = z3
	       
	   %    Sol = {ChoiceFromList {Substitute [genvar(x y) x [x y x]] x X}}
	    %   Sol = {ChoiceFromListP {Substitute [[1 [1 [1 2]]] [3 4] [5 6]] [1 2] x}}
	       %Sol = {Substitute {ChoiceFromListP [u(genvar(domain:[1 2]) genvar(domain:[1 2]))]} 1 one}
	      % Sol = {List.map [genvar(domain:[3 2]) genvar(domain:[4 5])] fun {$ A} {ChoiceFromListP A} end }
		      % Sol = Sol2
	        Sol = {MakeChoiceNet [u([genvar(domain:[1 2]) a]) genvar(domain:[3 4])]}
		   end }}
	       
 



{Browse {ChoiceNet a(x:f)}}



fun {SubstituteOne Expr}
   % Returns a substitution of the expression in Expr
   % variables genvar are being substituted.
   
   
   GenvarList Values in 
   GenvarList = {GetGenvars Expr}
   Values = {SearchOne proc {$ Sol} Sol = {MakeChoiceNet GenvarList} end}.1
   {Subst2 Expr {List.zip GenvarList Values fun {$ G V} G#V end}}
end

fun {SubstituteAll Expr}
   % Returns all possible substitutions.

   GenvarList Values in
   GenvarList = {GetGenvars Expr}
   Values = {SearchAll proc {$ Sol} Sol = {MakeChoiceNet GenvarList} end}
   {List.map Values fun {$ L} {Subst2 Expr {List.zip GenvarList L fun {$ G V} G#V end}} end}
end

   

{Browse {SubstituteAll [u([[genvar(domain:[3 2])]] genvar(domain:[1 4]))]}}
{Browse {SubstituteAll [parent(genvar(domain:[mary ann])
			       genvar(domain:[ann mary]))
			child(genvar(domain:[ann mary])
			      genvar(domain:[mary ann]))]}}

{Browse {SubstituteAll [genvar(domain:[fun {$ A B} A+B end
				       fun {$ A B} A-B end ]
			      )]}}
{Browse {{SubstituteOne [genvar(domain:[fun {$ A B} A+B end
				       fun {$ A B} A-B end ]
			       )]}.1 1 2}}
%{ExploreAll proc {$ Sol} Sol =  point(x:choice 1 [] 2 end  y:choice 3 [] 4 end) end }


%fun {Generalize X Y}
   % Returns a generalization of X and Y.



fun {CP A B F}
 %  {Browse f(A B)}
   case f(A B)
   of f(H1|nil H2|nil) then
      {F H1 H2}|nil
   [] f(H1|T1 H2|nil) then
      {Append {F H1 H2}|nil {CP T1 H2|nil F}}
   [] f(H1|nil H2|T2) then
      {Append {F H1 H2}|nil {CP H1|nil T2 F}}
   [] f(H1|T1 H2|T2) then
      {Append
       {F H1 H2}|nil
       {Append 
        {CP H1|nil T2 F}
	{Append 
	 {CP T1 H2|nil F}
	 {CP T1 T2 F}
	}
       }
       }   
   else
      nil
   end
end

fun {Gen A1 A2}
   %% Generalization operator gen(a1, a2)
   % returns a generalization of gen(a1, a2) with
   % the help of the generalization variable record genvar(domain: [e1 e2 ...])

   if A1 == A2 then
      A1
   elseif {And {List.is A1} {List.is A2}} then
      if {List.length A1} == {List.length A2} then
	 H1 T1 H2 T2 in 
	 A1 = H1|T1
	 A2 = H2|T2
	 {Gen H1 H2}|{Gen T1 T2}
      else
	 genvar(domain:[A1 A2])
      end
   elseif {And {Record.is A1} {Record.is A2}} then
      
      if {Record.label A1}=={Record.label A2} then
	 if {Record.label A1}==genvar then
	    genvar(domain:{Append A1.domain A2.domain})
	 else  
	    {Record.zip A1 A2 fun {$ F1 F2} {Gen F1 F2} end}
	 end
	 
      elseif {Record.label A1}==genvar then
	 D1 in
	 A1 = genvar(domain: D1)
	 genvar(domain:{Append D1 A2|nil})
      elseif {Record.label A2}==genvar then
	 D2 in
	 A2 = genvar(domain: D2)
	 genvar(domain:A1|D2)
      elseif {And {Record.label A1}==clause {Record.label A2}==clause} then
	 Head1 Body1 Head2 Body2 in
	 A1 = clause(head:Head1 body:Body1)
	 A2 = clause(head:Head2 body:Body2)
	 
	 clause(head:{CP Head1 Head2 Gen} body:{CP Body1 Body2 Gen})
      else
	 genvar(domain:[A1 A2])
      end
   else
      genvar(domain: [A1 A2])
   end
end


{Browse {Gen [a b c] [1 2]}}
{Browse {Gen a(a:1 b:2 3) a(a:1 b:2)}}
{Browse {Gen [genvar(domain:[a b])] [genvar(domain:[b b])]}}
{Browse {Gen genvar(domain:[a b]) genvar(domain:[1 2])}}
{Browse {Gen genvar(domain:[a b]) c}}
{Browse {Gen c genvar(domain:[a b]) }}
{Browse {Gen
	 clause(head:[a(a b)] body:[b(1 2) c(1 2)])
	 clause(head:[a(c b)] body:[b(3 2) c(3 2)])}}


fun {CartesianProductApply A B F}
   {List.map A fun {$ I}
		  {List.map B fun {$ J}
				 {F I J}
			      end
		  }
	       end
    }
   
end


{Browse {CartesianProductApply [1 2 3] [1 2] fun {$ I J} I#J end}}


 


{Browse {CP [[ff fg] b c] [1 2] fun {$ I J}
 			    u(I J) end}}
      

fun {NewKB}
   {NewCell nil}
end

proc {AssertToKB KB X}
   if {Member X @KB} then
      skip
   else
	 KB:={Append @KB X|nil}
   end
end

proc {RetractFromKB KB X}
   if {Member X @KB} then
      H T in
      @KB = H|T
      if H == X then
	 KB := T
      else
	 KB := H|{List.filter T fun {$ I} I\=X end }
      end
   end
end



KB={NewKB}
{Browse @KB}
{AssertToKB KB 1}
{Browse @KB}
{AssertToKB KB 1}
{Browse @KB}
{AssertToKB KB 2}
{Browse @KB}
{RetractFromKB KB 2}
    {Browse @KB}


fun {TestUnify A B }
   try
      A = B
   catch X then nil
   end
end



   

% fun {Query KB Y}
%    {List.filter @KB
%     fun {$ I}
%        local X
%        in
% 	  X = {NewCell @Y}
% 	  {Browse {IsFree Y}}
%        {Browse testing#I}
%        case {TestUnify I @X}
%        of nil then
% 	  {Browse I#' does not unify with '#@X}
% 	  false
%        [] J then true
%        end
%        end
%     end
%     }
% end

fun {Query KB X}
   X1 in
   {CopyTerm X X1}
   {SearchAll
    proc {$ Sol}
       Sol = {ChoiceFromList KB}
       Sol = f(_ _)
    end
    }
end


% fun {Query KB X}
%    {List.filter @KB
%     proc {$ I O}
%        K in
%        {Space.new
% 	fun {$}
% 	   {Browse testing#I#X}
% 	   X1 in
% 	   X1 = {X clone($)}
% 	   case {TestUnify I X1}
% 	   of nil then
% 	      false
% 	   []
% 	      J then true
% 	   end
% 	end
% 	K
%        }
%        {Space.merge K O}
%     end
%    }
% end

{List.forAll [f(a b) f(1 2) c(1 2) d 2 3] proc {$ I} {AssertToKB KB I} end}
{Browse @KB}



{Browse {TestUnify f(1 f(1 2)) f(1 _)}}
{Browse {CopyTerm f(_ a [_] _) $}}
{Browse query#{Query @KB a}}
