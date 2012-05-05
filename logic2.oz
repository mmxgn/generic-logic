declare
%% TODO: Resolutions
%% try solving it with search
%% Gia forward chaining: assert/2 assert_and_fc/3
%% assert_and_fc: trekse ena fc gia na deis ti kainourgia paragontai
%% pretend_assert_and_fc: trekse se ena copy, des ti tha paragotaner

%% Helper Functions


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


proc {BeginsWithUppercase A ?B}
    First
    Uppercase = "ABCDEFGHIJKLMNOPQRSTUVWXYZ"   
    Tostring = {Atom.toString A }
    in
    Tostring = First|_
    
    if {Member First Uppercase} then
       B = true
    else
       B = false
    end
 end

proc {DoesNotBeginWithUppercase A ?B}
   B = {Not {BeginsWithUppercase A}}
end

   
fun {ChoiceFromList L}
   % Generate a tree of choice points
   % from a list L.
   case L
   of nil then fail
   [] H|T then
      choice H
      [] {ChoiceFromList T} end
   else
      L
   end
end


fun {SearchSubsets L N}
   % Returns all subsets within L of size N
   {SearchAll
    proc {$ Sol} 
       SolT in 
       SolT = {FD.list N 1#{List.length L}}
       {FD.distinct SolT}
       for K in 1..{List.length SolT}-1 do
	  {Nth SolT K} <: {Nth SolT K+1}
       end
       {FD.distribute naive SolT}
       {List.map SolT fun {$ I} {Nth L I} end Sol}
    end
   }
end

fun {SearchSublists L N}
   % Same as above, but can return tuples of the form
   % [a ... (N times) ... a]
   {SearchAll
    proc {$ Sol}
       SolT in
       SolT = {FD.list N 1#{List.length L}}
       {FD.distribute naive SolT}
       {List.map SolT fun {$ I} {Nth L I} end Sol}
    end
   }
end
   
fun {SearchAllSubsets L N}
   case N of
      0 then
      nil|nil
   else
      {List.append
       {SearchSubsets L N}
       {SearchAllSubsets L N-1}
      }
   end  
end


proc {ListNotIn A B ?T}
   % Returns true if none of the elements in A
   % appears in B

   for I in A break:Break do
      if {Member I B} then
	 T=false
	 {Break}
      end
   end

   try T=true
   catch _ then skip
   end
   
end


fun {ListInfix L E}
   % Infixes an element E between every pair of
   % elements in L.
   % i.e. if L=[a b c] and E=','
   % it returns [a ',' b ',' c]

   case L of
      nil then nil
   []
      A|nil then
      A|nil
   []
      A|T then
      A|E|{ListInfix T E} 
   end
	
end

fun {ListRemoveAll L P}
% Switches all instances of P from list L, searches one level only.

   case L
   of nil then
      nil
   [] H|T then
      if H == P then
	 {ListRemoveAll T P}
      else
	 H|{ListRemoveAll T P}
      end
   else
      L
   end
end
fun {ListRemoveDuplicates L}
   case L
   of nil then
      nil
   []
      H|T then
      H|{ListRemoveDuplicates {ListRemoveAll T H}}
   else
      L
   end
end
fun {ListFlattenOne L}
   % Flattens a list of lists, but keeps flattening to one level only.
   case L of nil then nil
   []
      L = H|T then {List.append H {ListFlattenOne T}}
   end
end
fun {SetIntersection S1 S2}
   {List.filter S1 fun {$ I} {List.member I S2} end}
end
fun {SetUnion S1 S2}
   {ListRemoveDuplicates {List.append S1 S2}}
end
fun {SetDifference S1 S2}
   {List.filter S1 fun {$ I}
			  {List.member I S2} == false
		       end
       }
end


class RCL from BaseObject
	     %% Relational Clausal Logic grammar
	     %
	     % Syntax:
	     %
	     %         constant --> oz atom that does not begin with upper case
	     %         variable --> oz atom that begins with upper case
	     %         term     --> constant
	     %                      | variable
	     %         predicate --> constant
	     %         atom      --> functor where each element is a term
	     %         clause    --> head [:- body]
	     %         head      --> [atom[;atom]*]
	     %         body      --> atom[,atom]*
	     %
	     % i.e.    "Peter likes anybody who is his student. Maria is a student of peter."
	     % becomes: likes(peter,'S') :- student_of('S',peter).
	     %          student_of(maria,peter).

   meth init()
      skip
   end

   meth constant(C)
      if {Atom.is C} andthen {DoesNotBeginWithUppercase C} then
	 skip
      else
	 fail
      end
   end

   meth isConstant(C B)
      if {Atom.is C} andthen {DoesNotBeginWithUppercase C} then
	 B = true
      else
	 B = false
      end
   end
   
   meth variable(V)
      if {Atom.is V} andthen {BeginsWithUppercase V} then
	 skip
      else
	 fail
      end
   end

   meth isVariable(V B)
      if {Atom.is V} andthen {BeginsWithUppercase V} then
	 B=true
      else
	 B=false
      end
   end
   
   meth term(T)
      choice
	 {self constant(T)}
      []
	 {self variable(T)}
      end
   end

   meth isTerm(T B)
      if {self isConstant(T $)} orelse
	 {self isVariable(T $)} then
	 B=true
      else
	 B=false
      end
   end
   
   meth predicate(P)
      {self constant(P)}
   end

   meth isPredicate(P B)
      if {self isConstant(P $)}
      then
	 B = true
      else
	 B = false
      end
   end
   
   meth atom(A)
      if {Record.is A}==false then
	 {self predicate(A)}
      else
	 {Record.forAll A proc {$ F}
			     {self term(F)}
			  end
	 }
      end
   end

   meth isAtom(A B)
	 fun {IsTermList L}
	    case L of nil
	    then true
	    []
	       H|T then
	       {self isTerm(H $)} andthen {IsTermList T}
	    end
	 end
      in
      if {Record.is A}==false
      then
	 if {self isPredicate(A $)} then
	    B = true
	 else
	    B = false
	 end
      else
	 B = {IsTermList
	      {Record.toList A}
	     }
      end
   end
   
	 

   meth clause(C)
      case C of [H] then {self head(H)}
      []
	 ':-'|B then {self body(B)}
      else 
	 HeadT BodyT in
	 {List.takeDropWhile C fun {$ I} I\=':-' end HeadT _|BodyT}
	 {self head(HeadT)}
	 {self body(BodyT)}
      end
   end

   meth isClause(C B)
      case C of [Head] then B = {self isHead(Head $)}
      []
	 ':-'|Body then B = {self isBody(Body $)}
      else
	 HeadT BodyT in
	 {List.takeDropWhile C fun {$ I} I\=':-' end HeadT _|BodyT}
	 B = {self isHead(HeadT $)} andthen 
	 {self isBody(BodyT $)}
      end
   end
   

   meth splitClause(C Head Body)
      case C of [H] then Head=[H] Body=nil
      []
	 ':-'|B then Head=nil Body={List.filter B fun {$ I} I\=',' end}
      else
	 HeadT BodyT in
	 {List.takeDropWhile C fun {$ I} I\=':-' end HeadT _|BodyT}
	 Head = {List.filter HeadT fun {$ I} I\=';' end}
	 Body = {List.filter BodyT fun {$ I} I\=',' end}
      end
   end

   meth getConstantsFromAtom(A Cl)
      TermList in
      if {self isAtom(A $)} then
	 TermList = {Record.toList A}
	 Cl = {List.filter TermList fun {$ I}
			      {self isConstant(I $)}
			   end
	      }
      else
	 Cl = nil
      end
   end
   
   meth head(H)
      case H of
	 nil then skip
      else
	 {self atomDisjList(H)}
      end
   end

   meth isHead(H B)
      case H of
	 nil then B=true
      else
	 B = {self isAtomDisjList(H $)}
      end
   end

   meth body(B)
      {self atomConjList(B)}
   end

   meth isBody(Body B)
      B = {self isAtomConjList(Body $)}
   end
   

   meth atomDisjList(ADL)
      choice
	 ADL2 in ADL = [ADL2]	
	 {self atom(ADL2)}
      []
	 A ADL2 in
	 ADL = {List.append [A ';'] choice ADL2 [] [ADL2] end}
	 {self atom(A)}
	 {self atomDisjList(ADL2)}
      end
   end

   meth isAtomDisjList(ADL B)
      case ADL
      of [ADL2] then
	 B = {self isAtom(ADL2 $)}
      else
	 A ADL2 in 
	 if ADL == {List.append [A ';'] ADL2} orelse
	    ADL == {List.append [A ';'] [ADL2]} then
	    B = {self isAtom(A $)} andthen {self isAtomDisjList(ADL2 $)}
	 else
	    B = false
	 end
      end
   end
   
      
   meth atomConjList(ACL)
      choice
	 ACL2 in ACL = [ACL2]
	 {self atom(ACL2)}
      []
	 A ACL2 in	 
	 ACL = {List.append [A ','] choice ACL2 [] [ACL2] end}
	 {self atom(A)}
	 {self atomConjList(ACL2)}
      end
   end
   
   meth isAtomConjList(ACL B)
      case ACL
      of [ACL2] then
	 B = {self isAtom(ACL2 $)}
      else
	 A ACL2 in 
	 if ACL == {List.append [A ','] ACL2} orelse
	    ACL == {List.append [A ','] [ACL2]} then
	    B = {self isAtom(A $)} andthen {self isAtomDisjList(ACL2 $)}
	 else
	    B = false
	 end
      end
   end
   
  

   meth herbrandUniverse(P Hu)
      fun {GetConstantsFromListOfAtoms L}
	 case L of nil then nil
	 [] H|T then
	    {SetUnion
	     {self getConstantsFromAtom(H $)}
	     {GetConstantsFromListOfAtoms T}
	    }
	 end
      end
      
      fun {GetAtomsFromListOfClauses L}
	 Head Body in
	 case L of nil then nil
	 []
	    
	    H|T then
	    {self splitClause(H Head Body)}
	    {SetUnion
	     {SetUnion Head Body}
	     {GetAtomsFromListOfClauses T}
	    }
	 end	 
      end	 
   in
      Hu = {GetConstantsFromListOfAtoms
       {GetAtomsFromListOfClauses P }
       }
   end


   meth herbrandBase(P Hb)
      fun {GetAtomsFromListOfClauses L}
	 Head Body in
	 case L of nil then nil
	 []
	    
	    H|T then
	    {self splitClause(H Head Body)}
	    {SetUnion
	     {SetUnion Head Body}
	     {GetAtomsFromListOfClauses T}
	    }
	 end	 
      end
      fun {ChoiceFromList L}
	 case L of
	    nil then fail
	 [] H|T then
	    choice H [] {ChoiceFromList T} end
	 end
      end
      
      fun {GetPredicateListBase Pl Hu}
	 case Pl of
	    nil then nil
	 []
	    H|T then
	    
	    {SetUnion
	     {SearchAll fun {$}
			   {Record.map H
			    fun {$ _}
			       {ChoiceFromList Hu}
			    end
			   }
			end
	     }
	     {GetPredicateListBase T Hu}
	    } 
	 end
      end
      
      Hu Al in
      Hu = {self herbrandUniverse(P $)}
      Al = {GetAtomsFromListOfClauses P}
      Hb = {GetPredicateListBase Al Hu}
   end

   meth herbrandInterpretations(P Hi)
      Hb in
      {self herbrandBase(P Hb)}
      Hi = {SearchAllSubsets Hb {List.length Hb}}
   end
   

   meth getAllPossibleSubstitutions(Clist Variables Substitutions)
      % Given a list of constants Clist and a list of variables in Variables
      % binds Substitutions to all the possible substitution sets
      fun {TlistToSubst Tlist Subst}
	 case Tlist of nil then nil
	 []
	    Ht|Tt then
	    Hs Ts in
	    Subst = Hs|Ts
	    Ht#Hs|{TlistToSubst Tt Ts}
	 end   
      end
      
      Termset in
          
      Termset = {SearchSublists Clist {List.length Variables}}

      Substitutions = {List.map
		       Termset
		       fun {$ T}
			  {TlistToSubst Variables T}
			  
		       end
		      }
   end

   meth getVariablesFromClause(Clause Varlist)
      % Returns all the variables from a clause
      % Clause in Varlist.
      
      fun {GetVarHelper L}
	 case L of nil then nil
	 []
	    H|T then
	    if {self isAtom(H $)} then
	       {SetUnion {Record.toList {Record.filter
			  H
			  fun {$ T}
			     {self isVariable(T $)}
			  end
			 }}
		{GetVarHelper T}
	       }       
	    end
	 end
      end
      
      Head Body in
      {self splitClause(Clause Head Body)}
      Varlist = {SetUnion
		 {GetVarHelper Head}
		 {GetVarHelper Body}
		 }
   end
   

   meth getClauseInstances(Clause Clist Instances)
      % Given a constant list Clist and a clause Clause
      % returns all the possible substitutions of the variables
      % found in Clause from Clist.
      Varlist Substitutions in
      
      Varlist = {self getVariablesFromClause(Clause $)}
      Substitutions = {self getAllPossibleSubstitutions(Clist Varlist $)}

      Instances = {List.map Substitutions
		   fun {$ Sub}
		      {self substituteOne(Clause Sub $)}
		   end
		  }
      
   end

   meth isClauseModel(Clause Interpretation B)
      Instances Iu
      fun {GetConstantsFromListOfAtoms L}
	 case L of nil then nil
	 [] H|T then
	    {SetUnion
	     {self getConstantsFromAtom(H $)}
	     {GetConstantsFromListOfAtoms T}
	    }
	 end
      end
      proc {ClauseModelHelper Interpretation Instances B}
	 case Instances of nil then B=true
	 []
	    H|T then
	    Head Body in
	    H = {self splitClause($ Head Body)}
	    B = {SetIntersection Head Interpretation} == Head orelse
	    {SetIntersection Body Interpretation} == nil andthen
	    {ClauseModelHelper Interpretation T}
	 end
      end
   in
      Iu = {GetConstantsFromListOfAtoms Interpretation}
      Instances = {self getClauseInstances(Clause Iu $)}
      B = {ClauseModelHelper Interpretation Instances}
   end
   
   meth clauseModels(Clause Program Models)
      Hi in
      Hi = {self herbrandInterpretations(Program $)}
      Models = {List.filter
		Hi
		fun {$ I}
		   {self isClauseModel(Clause I $)}
		end
	       }
      
   end

   meth isProgramModel(Program Interpretation B)
      fun {ProgramModelsHelper Program Interpretation}
	 case Program of nil then true
	 []
	    H|T then
	    {self isClauseModel(H Interpretation $)} andthen
	    {ProgramModelsHelper T Interpretation}
	 else
	    false
	 end
      end
   in
      
      B = {ProgramModelsHelper Program Interpretation}
   end
   
   meth programModels(Program Models)
      Hi 
      fun {ProgramModelsHelper Program Interpretation}
	 case Program of nil then true
	 []
	    H|T then
	    {self isClauseModel(H Interpretation $)} andthen
	    {ProgramModelsHelper T Interpretation}
	 else
	    false
	 end
      end
   in
      Hi = {self herbrandInterpretations(Program $)}
      Models = {List.filter
		Hi
		fun {$ I}
		   {ProgramModelsHelper Program I}
		      
		end
	       }
   end
   
   meth substituteOne(C S Out)
      % Implements substitution.
      % [todo: add decprog_all.pdf source here]
      % A substitution is a mapping \sigma (here S)
      % that is of the form Var --> Trm (here [v1#t1 v2#t2 ... vn#tn])
      % so that, for a Clause C, the result of \sigma on C
      % denoted as C\sigma is obtained by replacing all
      % occurences of X \in Var by \sigma(X).
      % C\sigma is an instance of C
      %
      % i.e.
      % if S=['X'#maria] and
      % C=[likes(peter 'S') ':-' student_of('S' peter)]
      % then
      % {<RCL object> substitute(C S Out)} binds Out to
      % [likes(peter maria) ':- ' student_of(maria peter)]

      proc {IsListOfTerms L ?B}
	 case L of nil
	 then
	    B = true
	 []
	    H|T then

	    Var Term in
	    H = Var#Term
	    B = {self isVariable(Var $)}
	    andthen {self isTerm(Term $)}
	    andthen {IsListOfTerms T}
	 end
      end
   in
      if {IsListOfTerms S} then %%TODO: test isClause
	 Out = {Subst2 C S}
      else
	 raise cannotsubstitute(C S) end
      end
      
   end
   
end

   
	     
class PCL from BaseObject
	     %% Propositional Clausal Logic grammar
	     %
	     % Syntax:
	     %         Clause --> Head
	     %                    | Head :- Body
	     %
	     %         Head   --> nil
	     %                    | Atom [;Atom]*
	     %
	     %         Atom   --> (Valid Oz Atom)
	     
   meth init()
      skip
   end

   meth splitclause(C Head Body)
   %   {Browse C}
      case C
      of
	 [H] then
	 Head = [H]
	 Body = nil
      [] ':-'|B then
%	 {Browse B}
	 Head = nil
	 Body = {List.filter B fun {$ K} K\=',' end}
      else
	 if {List.member ':-' C} then
	    HeadT BodyT
	    in
	    {List.takeDropWhile C fun {$ I} I\=':-' end HeadT _|BodyT}
	    Head = {List.filter HeadT fun {$ K} K\=';' end}
	    Body = {List.filter BodyT fun {$ K} K\=',' end}
	 else
	    Head = {List.filter C fun {$ K} K\=';' end}
	    Body = nil
	 end
	 
      end
      
   end
   
   meth clause(C)
 %     {Browse clause(C)}
      choice
	 %{Browse chice(head(C))}
	 {self head(C)}
	 %{Browse done}
      []
	 %{Browse els}
	 H B in
	 %{Browse H}
	 %{Browse B}

	 choice [H] = C
%	    {Browse choose(1)}
	    {self head(H)}
%	    {Browse success(1)}
	 []
%	    {Browse choose(2)}
	    C = ':-'|B
	    {self body(B)}
%	    {Browse success(2)}
	 []
%	    {Browse choose(3)}
	    {List.takeDropWhile C fun {$ I} I\=':-' end H _|B} % Splits the clause to head and body.
	    {self head(H)}
	    {self body(B)}
%	    {Browse success(3)}
	    
	 end
	 
	 
	 %{Browse hh(H)}
	 %{Browse bb(B)}
	 
%	 {Browse chice([head(H) ':-' body(B)])}

%	 {self head(H)}
%	 {self body(B)}

      end
   end

   meth body(B)
      %{Browse body(B)}
      {self atomConjList(B)}
   end
   

   meth head(H)
      %{Browse head(H)}
      {self atomDisjList(H)}
   end

   meth atom(A)
      if
	 {Atom.is A} == true
      then skip
      else	 
	 fail
      end
   end

   

   % meth atomDisjList(ADL)
   %    choice
   % 	 A in
   % 	 ADL=[';' A]
   % 	 {self atom(A)}
   %    []
   % 	 A ADL2 in
   % 	 ADL = {List.append [';' A] ADL2}
   % 	 {self atom(A)}
   % 	 {self atomDisjList(ADL2)}
   %    end
   % end

   meth atomDisjList(ADL)
      choice
	 ADL2 in ADL = [ADL2]
	
	 {self atom(ADL2)}
      []
	 A ADL2 in
	 ADL = {List.append [A ';'] choice ADL2 [] [ADL2] end}
%	 {List.takeDropWhile ADL fun {$ I} I \= ';' end A _|ADL2}
	 {self atom(A)}
	 {self atomDisjList(ADL2)}
      end
   end
   

   meth atomConjList(ACL)
      choice
	 ACL2 in ACL = [ACL2]
	 {self atom(ACL2)}
      []
	 A ACL2 in
	 
	 ACL = {List.append [A ','] choice ACL2 [] [ACL2] end}
	 {self atom(A)}
	 {self atomConjList(ACL2)}
      end
      
   end

   meth isValidClause(C T)
      case {SearchOne
	    fun {$}
	       {self clause(C)}
	       C
	    end
	   }
      of nil then T=false
      else
	 T=true
      end
   end
   
   meth isValidAtom(A T)
      case {SearchOne
	    fun {$}
	       {self atom(A)}
	       A
	    end
	   }
      of nil then T=false
      else
	 T=true
      end
   end

   meth getAtomsFromClause(C Al)
      case {self isValidClause(C $)}
      of false then
	 raise invalidClause(C) end
      else
	 Al = {List.filter C
	       fun {$ I}
		  {self isValidAtom(I $)} andthen I\=';' andthen I\=',' andthen I\=':-' 
	       end
	      }
      end
   end

   meth newClause(H B C)
      if H == nil andthen B == nil then
	 C = nil
      elseif H == nil then
	 C = {List.append ':-'|nil
	      {ListInfix B ','}
	     }
      elseif B == nil then
	 C = {ListInfix H ';'}
      else
	 C = {List.append
	      {List.append
	       {ListInfix H ';'}
	       ':-'|nil
	      }
	      {ListInfix B ','}
	     }
      end
   end

   meth negateClause(C NCl)
      % Negates a clause. NCl is the list
      % of produced clauses.

      H B NCl2 in
      {NewCell nil NCl2}
      
      {self splitclause(C H B)}
      for E in H do
	 NCl2 := {List.append @NCl2 [[':-' E]]}
      end

      for E in B do
	 NCl2 := {List.append @NCl2 [[E]]}
      end
      
      NCl = @NCl2
   end
   
end

   
class KnowledgeBase from BaseObject
   attr Base:nil Grammar
      HerbrandBase:nil HerbrandInterpretations:nil
      
   meth init(G)
      Base := nil
      Grammar := {New G init()}
      HerbrandBase := nil
      HerbrandInterpretations := nil
   end
  
   meth assert(X)
      %% Asserts X in the knowledge base
      % only if X is not already there and
      % X is a valid clause.
      
      if {Member X @Base} then
	 skip                              % Do nothing if X is already in the knowledge base.
      else
	 case {SearchOne                   % See if X is a valid clause
	       fun {$}
		  {@Grammar clause(X)}
		  X
	       end
	      }
	 of nil then skip
	 else
	    Base := {List.append @Base X|nil}
	 end
      end

      % Calculate new herbrand base and interpretations.
      HerbrandBase := {List.append @HerbrandBase {self getAtomsFromClause(X $)}}
      HerbrandInterpretations := {self getHerbrandInterpretations($)}
   end

   meth retract(X)
      Base := {List.filter @Base
	       fun {$ I}
		  I \= X
	       end
	      }
      HerbrandBase := {SetDifference @HerbrandBase {self getAtomsFromClause(X $)}}
      HerbrandInterpretations := {self getHerbrandInterpretations($)}
   end


   
 %  meth getAtoms(L)
 %     L = {List.filter @Base fun {$ I}
%				{Atom.is I}
%			     end
%	  }
 %  end

   meth getClauses(L)
      L = {List.filter @Base fun {$ I}
				{self isValidClause(I $)}
			     end
	  }
   end
   
      
   meth getAtoms(L)
      % L = {List.filter @Base fun {$ I}
      % 				{self isValidClause(I $)}
      % 			     end
      % 	  }

      L = {ListRemoveDuplicates {ListFlattenOne {List.map @Base
	   fun {$ I}
	      if {self isValidClause(I $)} then
		 {self getAtomsFromClause(I $)}
	      end
	   end
						}
				}
	   }
   end

   meth getGrammar(G)
      G = Grammar
   end

   meth isValidAtom(A T)
      {@Grammar isValidAtom(A T)}
   end

   meth isValidClause(C T)
      {@Grammar isValidClause(C T)}
   end
   
   meth getAtomsFromClause(C Al)
      {@Grammar getAtomsFromClause(C Al)}
   end

   meth getHerbrandBase(B)
      {self getAtoms(B)}
   end

   meth getHerbrandInterpretations(HI)
      B in {self getHerbrandBase(B)}
      HI = {SearchAllSubsets B {List.length B}}
   end

   meth isModelForClause(I C B)
      Head Body in
      {@Grammar splitclause(C Head Body)}
      %B = clause(head:Head body:Body)
      if {SetIntersection I Head}\=nil
	 orelse {SetIntersection I Body}\={List.filter Body fun {$ J}
							       J\=','
							    end
					  }
							    then
	 B = true
      else
	 B = false
      end
   end

 %  meth getModelsForClause(C M)
 %     Cl = {self getClauses($)}
      
   meth getModelsForClause(Il C M)
      M = {List.filter Il fun {$ J}
			     {self isModelForClause(J C $)}
			  end
	   }
   end

   meth getModels(M)
      M = {List.filter @HerbrandInterpretations
	   fun {$ J}
	      {self isModel(J $)}
	   end
	  }
   end
   
   
   meth isModel(I B)
      Cl in
      Cl = {self getClauses($)}

      if {ListRemoveDuplicates {List.map Cl
       fun {$ J}
	  if {self isModelForClause(I J $)} then
	     nil
	  else
	     J
	  end
       end
	 }} == [nil] then
	 B = true
      else
	 B = false
      end
      
   end

   meth resolve(Ci Cj Ck)
      Hi Bi
      Hj Bj
      Hk Bk
      Inters1
      Inters2
      Inters
   in
      {@Grammar splitclause(Ci Hi Bi)}
      {@Grammar splitclause(Cj Hj Bj)}
      

      Inters1 = {SetIntersection Hi Bj}
      Inters2 = {SetIntersection Hj Bi}
      Inters = {SetUnion Inters1 Inters2}
      Ck = {@Grammar newClause(
			{SetUnion
			 {SetDifference Hi Inters}
			 {SetDifference Hj Inters}
			}
			{SetUnion
			 {SetDifference Bi Inters}
			 {SetDifference Bj Inters}
			 }
			 $)
	   }
      
      
      
   end
   
  %  meth resolutionRule1(C1 C2 C3)
 %      H1 B1
 %      H2 B2
 %      H3 B3
 %      C3T
 %   in
 % %     {Browse c1#C1}
 % %     {Browse c2#C2}
 %      {@Grammar splitclause(C1 H1 B1)}
 %      {@Grammar splitclause(C2 H2 B2)}
 %      {Browse h1#H1}
 %      {Browse b1#B1}
 %      {Browse h2#H2}
 %      {Browse b2#B2}
      
 %      for E in H1 break:Break do
 % 	 if {List.member E B2} then
 % 	    H3 = {List.filter {SetUnion H1 H2} fun {$ K} K\=E end}
 % 	    {Browse h3#H3}
 % 	    B3 = {List.filter {SetUnion B1 B2} fun {$ K} K\=E end}
 % 	    {Browse b3#B3}
 % 	    C3 = {@Grammar newClause(H3 B3 $)}
 % 	    {Browse c3#C3}
 % 	    {Break}
	    
 % 	 end
 %      end
 %     for E in H2 break:Break  do
%	 if {List.member E B1} then
%	    H3 = {List.filter {SetUnion H1 H2} fun {$ K} K\=E end}
%	%    {Browse h3#H3}
%	    B3 = {List.filter {SetUnion B1 B2} fun {$ K} K\=E end}
%	  %  {Browse b3#B3}
%	    C3 = {@Grammar newClause(H3 B3 $)}
%%   {Browse c3#C3}
%	    {Break}
%	    
%	 end
%      end
      
   %    try
   % 	 C3 = res_failed
   %    catch X then skip end
   %   % {Browse final#c3#C3}
      
      
      
      
   % end

   meth prove(C B)
      proc {ResolveH L Ci Pnew ?B}
	 for Cj in Pnew break:Break continue:Continue do
	    Ck Hi Hj Bi Bj in
	    {@Grammar splitclause(Ci Hi Bi)}
	    {@Grammar splitclause(Cj Hj Bj)}
	    {self resolve(Ci Cj Ck)}
%	    {Browse L#resolve(Ci Cj Ck)}
	     

	    if Ck == nil then
	       B = true
	       {Break}
	    elseif
	       Ck == {@Grammar newClause(
				  {SetUnion Hi Hj}
				  {SetUnion Bi Bj}
				  $
				  )}
	       
	    then
	      % B = false
	       {Continue}
	    else
	       B = {ResolveH L+1 Ck Pnew}
	    end
	 end
	 try
	    B = failed_to_apply_resolution(Ci)
	 catch _ then skip
	 end
	 
      end

      Cneg = {@Grammar negateClause(C $)}
      Pnew = {List.append
	      {self getClauses($)}
	      Cneg
	     }
   in
      for Ci in Cneg do
	 if {ResolveH 1 Ci Pnew} \= true then
	    B = false
	 end
      end

      try B=true
      catch _ then skip end
      
   end
   
   % meth proveBySearch(C B)
   %    fun {ProveHelper L Ci Cj}
   % 	 Ck in 
   % 	 if Cj == nil then
   % 	    false
   % 	 else
   % 	    {self resolutionRule1(Ci Cj Ck)}
   % 	    {Browse 1#step(L)#resolutionRule1(Ci Cj Ck)}
   % 	    case Ck of nil then true
   % 	    [] res_failed then
   % 	       Ck2 in
   % 	       {self resolutionRule1(Cj Ci Ck2)}
   % 	       {Browse 2#step(L)#resolutionRule1(Cj Ci Ck2)}
   % 	       case Ck2 of nil then true
   % 	       []
   % 		  res_failed then false
   % 	       else
   % 		  {ProveHelper L+1 Ck2 Cj}
   % 	       end
	       
   % 	    else
   % 	       {ProveHelper L+1 Cj Ck}
	       
   % 	    end
   % 	 end
   %    end
   %    Pnew Cneg
   % in
   %    Cneg = {@Grammar negateClause(C $)}
   %    Pnew = {List.append
   % 	      {self getClauses($)}
   % 	      {@Grammar negateClause(C $)}
   % 	     }
   %    for I in Pnew break:B0 do
   % 	 for J in Pnew break:B1 do
   % 	    if {ProveHelper 1 I J} orelse {ProveHelper 1 J I} then
   % 	       B = true
   % 	       {B0}
   % 	    end
   % 	 end
   %    end

   %    try
   % 	 B = false
   %    catch _ then skip end
      

	  
	   
		      
      
      
      
   % end
   
   % meth prove(C B)
   %    P Pold Pnew Cneg in
   %    P = {self getClauses($)}
   %    Cneg = {@Grammar negateClause(C $)}
   %    Pold = {Cell.new nil}
   %    Pnew = {Cell.new P}
   %    Pnew := {List.append @Pnew Cneg}
   %    {Browse first_pnew#@Pnew}

   %    for until:@Pnew==@Pold orelse @Pnew==[nil] break:B0 do
   % 	 Pold := @Pnew
   % 	 for I in @Pnew break:B1 do
   % 	%    {Browse i#I}
   % 	    for J in {List.filter @Pnew fun {$ K} K\=I end} break:B2 do
   % 	   %    {Browse j#J}
   % 	       C3 in
   % 	       {self resolutionRule1(I J C3)}
   % 	       {Browse res#C3#i#I#j#J}
   % 	       if C3 \= res_failed then
   % 		  Pnew := {List.filter @Pnew fun {$ K} K\=I end}
   % 		  Pnew := {List.filter @Pnew fun {$ K} K\=J end}
   % 		  Pnew := {List.append @Pnew [C3]}
   % 		  {Browse pold#@Pold}
   % 		  {Browse newpnew#@Pnew}
   % 	%	  {B1}
   % 	       end
   % 	    end
   % 	 end
   %    end

   %    {Browse cneg#Cneg}
   %    {Browse pnew#@Pnew}
   %    if {ListNotIn Cneg @Pnew} then
   % 	 B=true
   %    else
   % 	 B=false
   %    end
      
 %     if @Pnew==@Pold andthen @Pnew\=[nil] then
%	 if {ListNotIn Cneg @Pnew} then
%	    B=true
%	 else
%	    B=false
%	 end
	 
  %    elseif @Pnew==[nil] then
%	 B=true
   %   end
      
 %  end
   
 
      


   
end



% Set up a new Propositional Clausal Logic Knowledge base

PCLKB = {New KnowledgeBase init(PCL)}

% Assert some facts in it.

{List.forAll
 [
  [happy ':-' has_friends]
  [friendly ':-' happy]
  [wet ':-' rains]
  [':-' wet]


 ]
 proc {$ I}
    {PCLKB assert(I)}
 end
}

% Prove takes place with resolution by refutation

{List.forAll
 [
  [friendly ':-' has_friends]
  [friendly]
  [':-' rains]
 ]
 proc {$ I}
    {Browse prove(I)}
    {Browse
     {PCLKB prove(I $)}
    }
 end
}

{Browse {BeginsWithUppercase 'voltage'}}
 
    
RCL1 = {New RCL init()}
{ExploreOne fun {$}
	       T = clause([likes(peter 'S') ':-' student_of('S' peter)])
	       in
	       {RCL1 T}
	       T
	    end
}


Clause =  [likes(peter 'S') ':-' student_of('S' peter)]
H B

Program = [
	   [likes(peter 'S') ':-' student_of('S' peter)]
	   [student_of(maria peter)]
	  ]



in 
{RCL1 splitClause(Clause H B)}
{Browse H#B}
{Browse {RCL1 herbrandUniverse([Clause] $)}}
{Browse {RCL1 getConstantsFromAtom(student_of(maria peter) $)}}
{Browse {RCL1 herbrandUniverse([Clause [student_of(maria peter)]] $)}}
{Browse {RCL1 herbrandBase([Clause [student_of(maria peter)]] $)}}
{Browse {RCL1 herbrandInterpretations([Clause] $)}}
{Browse {Record.map func(a b c d) fun {$ _} '123' end}}
{Browse {RCL1 substituteOne([Clause] ['S'#maria] $)}}
%{Browse {RCL1 isModelForClause([likes(maria maria) sudent_of(maria peter)] Clause $)}}

{Browse {RCL1 getAllPossibleSubstitutions([maria peter] ['S' 'X'] $)}}
{Browse {RCL1 getVariablesFromClause([ma('X' ')')':-' b('X' '4') ',' c('Y' '5')] $)}}
{Browse {RCL1 getClauseInstances(Clause [maria peter] $)}}
{Browse {RCL1 isClauseModel(Clause [likes(peter maria) student_of(maria peter)] $)}}
%{Browse {RCL1 clauseModels(Clause [Clause [student_of(maria peter)]] $)}}
{Browse {RCL1 programModels(Program $)}}
{Browse {RCL1 isProgramModel(Program [student_of(maria peter)] $)}}