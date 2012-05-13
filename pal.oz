declare
L R1
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
in
L = [note(1 2) note(3 4) note(1 3)]

	
     


{ExploreAll proc {$ Sol}
	       Sol = note(_ _)
	       Sol = {ChoiceFromList [note(1 2) note(3 4)]}
	    end
 
}
	      
 