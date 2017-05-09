theory ExampleEventStructures
imports Enum EventStructures Relation Transitive_Closure String
begin

theorem emptyESValidES: "isValidES \<I>"
  apply(auto simp add: isValidES_def initialES_def isValidPO_def minimal_def isConfValid_def)
  apply(rule refl_Id)
     apply(rule trans_Id)
    apply(rule antisym_Id)
   apply(simp add: symmetriccl_def symmetric_symmetriccl)
   apply(simp add: sym_def trans_def irrefl_def)
  apply(simp add: trans_rtrancl)
  done
    
lemma initialConfig_no_read: "\<not> is_read x \<I>"
  apply(simp add: initialES_def)
  apply(simp add: is_read_def)
  done
    
theorem emptyESWellJustified: "well_justified \<I> \<C>"
  apply(auto simp add: well_justified_def)
  apply(rule emptyESValidES)
   apply(auto simp add: justified_def ae_justifies_subset_star_def)
  done
    
    
theorem emptyESJustEmptyES: "{} \<lesssim>\<^bsub>es\<^esub> {}"
  apply(auto simp add: justifies_config_inf_def justifies_config_subset_def justifies_config_def)
  done
    
end
  