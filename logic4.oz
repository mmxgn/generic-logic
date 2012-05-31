declare
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
HerbrandUniverse
fun {SearchVariableAll Domain}
   Dom
in
   Dom = 1#{List.length Domain}

   {SearchOne proc {$ Sol}
		 Sol = {FD.int Dom}
%		 Sol = {Nth Domain {FD.int Dom}}
		 {FD.distribute ff Sol}
	      end
    }
    
end

in

HerbrandUniverse = [ann mary john peter]

{Browse {SearchVariableAll HerbrandUniverse}}
