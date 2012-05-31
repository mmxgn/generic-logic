declare
   %% TODO: Add toString() method that
   % returns a pretty string for representation
   % purposes.

   % + generalize
   % i.e. variables of integers: FD.int
   %

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

class Predicate from BaseObject
		 
   attr
      Label
      TermList
      TermLabels

   meth init(L Tlist)
      Label := L
      TermList := Tlist
      TermLabels := nil
   end

   meth initFromRecord(R)
      Label := nil
      TermList := nil
      TermLabels := nil
      
      if {Atom.is R} then
	 Label := R
      elseif {Record.is R} then
	 Label := {Record.label R}
	 {Record.forAllInd R proc {$ I P}
				P2 in
				P2 = {New Predicate initFromRecord(P)}
				TermList := {List.append @TermList P2|nil}
				TermLabels := {List.append @TermLabels I|nil}
			     end
	  }
      end
      

      
   end
   
   meth getLabel(L)
      L = @Label
   end

   meth getChoicePoints(CP)
      CP = self
   end
   
   meth getTerms(T)
      T = @TermList
   end
   
   meth toString(S)
      Str in
      {NewCell nil Str}
      Str := {List.append
	      @Str
	       {Value.toVirtualString
		@Label
		1
		1
	       }
	     }

      if {List.length @TermList} > 0 then
	 Str := {List.append
		 @Str
		 "("
		}
	 for T in @TermList do
	    Str := {List.append
		    @Str
		    {List.append {T toString($)} ","}
		    }
	end

	 Str := {List.take @Str {List.length @Str}-1}

	 Str := {List.append
		 @Str
		 ")"
		}
      end
      
      S = {VirtualString.toString @Str}
      
   end
   
   meth arity(Arity)
      {List.length @TermList Arity}
   end

   meth isGround(B)
      fun {IsGround Tlist}
	 case Tlist
	 of nil then true
	 [] H|T then
	    {H isGround($)}
	    andthen
	    {IsGround T}
	 else
	    false
	 end
      end
   in
      B = {IsGround TermList}
   end

   meth getType(Type)
      Type = 'predicate'
   end

   meth unify(F1 U)
   %   {Browse {F1 getType($)}}
 %     if {F1 getType($)} == 'variable' then
%	 if {F1 inDomain(self $)} then
%	    D1 in
%	    D1 = {New Domain init([self])}
%	 
%	    U = {New Variable init({F1 getLabel($)} D1)}
%	 else
%	    U = nil
%	 end
      if {F1 getType($)} == 'variable' then
	 {F1 unify(self U)}
      
      
      elseif {F1 getType($)} == 'predicate' andthen {F1 getLabel($)} \= @Label then
	 U = nil
      elseif {F1 getType($)} == 'predicate' andthen @TermList == nil andthen
	 {F1 getTerms($)} == nil then
	 U = {New Predicate init(@Label @TermList)}
         
      else U = {New Predicate init(@Label {List.zip @TermList {F1 getTerms($)}
	   fun {$ T1 T2}
	      {T1 unify(T2 $)}
	   end
				     })}
      end
      
  %    elseif {F1 getType($)} == 'variable' then
%	 {F1 unify(self U)}
	 
	 
      
   end
   
end

class Domain from BaseObject
		
   attr D: nil

   meth init(Dom)
      D := Dom
   end

   meth has(X B)
      B = {Member X @D}
   end
   
      
   meth getChoicePoints(CP)
      CP = {ChoiceFromList @D}
   end
   
   
   meth append(V1)
      D := {List.append @D V1}
   end

   meth size(S)
      if {List.is @D} then S={List.length @D} else S=nil end
   end

   meth getDomain(Dom)
      Dom = @D
   end
      
end
   

class Variable from BaseObject
		  
   attr Label Domain: nil
      
   meth init(L D)
      Label := L
      Domain := D
   end

   meth toString(S)
      if {self isGround($)} then
	 S = {VirtualString.toString
	      {Value.toVirtualString
	       {@Domain getDomain($)}.1
	       1
	       1
	      }
	     }
      else
	 S = {VirtualString.toString
	      {Value.toVirtualString
	       @Label
	       1
	       1
	      }
	     }
      end
      
   end
   

   meth appendDomain(V)
      Domain := {@Domain append(V)}
   end

   meth inDomain(P B)
      B = {@Domain has(P $)}
   end
   
   meth changeLabel(L)
      Label := L
   end

   meth getLabel(L)
      L = @Label
   end
   
   
   meth getType(T)
      T = 'variable'
   end

   meth isGround(B)
      B = {@Domain size($)} == 1
   end

   meth getChoicePoints(CP)
      CP = {@Domain getChoicePoints($)}
      
   end

   meth unify(V2 CP)
      % Fix this
      CP2 in 
      CP2 = {@Domain getChoicePoints($)}
      CP2 = {V2 getChoicePoints($)}
      CP = {New Predicate init({CP2 getLabel($)} nil)}
   end
end

class Term from BaseObject
   attr Value

   meth init(V)
      Value := V
   end

   meth isVariable(B)
      B = {@Value getType($)} == 'variable'
   end

   meth isFunctor(B)
      B = {@Value getType($)} == 'functor'
   end

   meth isGround(B)
      B = {@Value isGround($)}
   end

   meth getType(T)
      T = 'term'#{@Value getType($)}
   end
end

% class Predicate from BaseObject
%    attr Value
%       TermList
%    meth init(V)
%       Value := V
%    end

%    meth getType(T)
%       T = 'predicate'
%    end
% end

class LogicAtom from BaseObject
   attr Predicate
      TermList
   meth init(P Tlist)
      Predicate := P
      TermList := Tlist
   end


   meth arity(A)
      {List.length TermList A}
   end

   meth isGround(B)
      fun {IsGround Tlist}
	 case Tlist
	 of nil then true
	 [] H|T then
	    {H isGround($)}
	    andthen
	    {IsGround T}
	 else
	    false
	 end
      end
   in
      B = {IsGround TermList}
   end

   meth getType(T)
      T = 'atom'
   end
end


class Clause
   attr Head
      Body
   meth init(H B)
      Head := H
      Body := B
   end

   meth appendHead(He)
      Head := {List.append @Head He}
   end
   
   meth appendBody(Be)
      Body := {List.append @Body Be}
   end

   meth isGround(B)
      fun {IsGround Tlist}
	 case Tlist
	 of nil then true
	 [] H|T then
	    {H isGround($)}
	    andthen
	    {IsGround T}
	 else
	    false
	 end
      end
   in
      B = {And
	   {IsGround Head}
	   {IsGround Body}
	   }
   end

   meth getType(T)
      if {List.length Head}==1 then
	 T = 'hornclause'
      else
	 T = 'clause'
      end
   end
end

class KnowledgeBase from BaseObject
   attr ListOfClauses: nil
      ListOfAtoms: nil
      ListOfPredicates: nil
      ListOfFunctors: nil

   meth assert()
      skip
   end

   meth assert_pretend()
      skip
   end

   meth retract()
      skip
   end

   meth bc_query()
      skip
   end

   meth fc_assert()
      skip
   end

   meth fc_assert_pretend()
      skip
   end

   meth fc_retract_pretend()
      skip
   end
end

F1 NewDomain NewVar F2 F3 NewVar2 NewDomain2 F4
P1 P2 in
F1 = {New Predicate init(blaz nil)}
P1 = {New Predicate initFromRecord(blah)}
P2 = {New Predicate initFromRecord(note(blah blah))}
{Browse {P1 toString($)}}
{Browse {P2 toString($)}}
NewDomain = {New Domain init([P1 P1])}
NewDomain2 = {New Domain init([P1 P1])}

NewVar = {New Variable init('X' NewDomain)}
NewVar2 = {New Variable init('Y' NewDomain2)}

F2 = {New Predicate init(note [NewVar2 NewVar2])}
F3 = {New Predicate init(note [NewVar NewVar])}
F4 = {New Predicate init(pause nil)}

%   {Browse {FD.decl} == {FD.decl}}
{Browse {F2 toString($)}}
{Browse {F3 toString($)}}
{Browse {NewVar toString($)}}
{Browse {F4 toString($)}}
{Browse 'p1unifyp1:'#{{P1 unify(P1 $)} toString($)}}
%{Browse 'var2unifyp1:'#{{P1 unify(NewVar $)} toString($)}}
{Browse {F2 arity($)}}
{Browse sss#{SearchAll proc {$ Sol}
		      Sol = {{P1 unify(NewVar $)} toString($)}
		   end
	}
}

{Browse {SearchAll proc {$ Sol}
	       Sol = {{F2 unify(F3 $)} toString($)}
	    end
}}
{Inspector.configure widgetShowVirtualStrings true}