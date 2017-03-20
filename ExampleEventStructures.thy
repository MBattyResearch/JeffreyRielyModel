theory ExampleEventStructures
imports Enum EventStructures Relation Transitive_Closure String
begin
  
value "refl {}"
value "top"
  
theorem "isValidPO {} {}"
  apply(simp add: isValidPO_def)
  oops
    
schematic_goal ex: "acyclic {(''a'', ''a'')} \<Longrightarrow> antisym ({(''a'', ''a'')}\<^sup>*)"
  by (rule Transitive_Closure.acyclic_impl_antisym_rtrancl)

theorem emptyESValidES: "isValidES empty_ES"
  apply(auto simp add: isValidES_def empty_ES_def isValidPO_def)
      defer
      apply(rule trans_Id)
     apply(simp add: antisym_def)
    apply(simp add: symmetric_def)
   apply(rule trans_Id)
  apply(rule refl_Id)
  done
     
theorem "well_justified empty_ES {}"
  apply(auto simp add: well_justified_def)
  apply(rule emptyESValidES)
  apply(auto simp add: empty_ES_def justified_def ae_justifies_star_def)
  done
