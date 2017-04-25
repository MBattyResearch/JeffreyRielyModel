theory ExampleEventStructures
imports Enum EventStructures Relation Transitive_Closure String
begin

theorem emptyESValidES: "isValidES empty_ES"
  apply(auto simp add: isValidES_def empty_ES_def isValidPO_def minimal_def isConfValid_def)
     apply(rule refl_Id)
    apply(rule trans_Id)
   apply(rule antisym_Id)
   apply(simp_all add: symmetriccl_def symmetric_symmetriccl)
   apply(simp_all add: symmetric_def trans_def irrefl_def)
  apply(auto)
  done

theorem emptyESWellJustified: "well_justified empty_ES {}"
  apply(auto simp add: well_justified_def)
  apply(rule emptyESValidES)
  apply(auto simp add: empty_ES_def justified_def ae_justifies_subset_star_def)
  done
