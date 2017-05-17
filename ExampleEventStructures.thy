theory ExampleEventStructures
imports Enum EventStructures Relation Transitive_Closure String
begin

interpretation emptyES: labelledES 
  "{(1,1)}\<^sup>*"  -- Order
  "{1}" -- Events
  "{}" -- Conflict
  "\<lambda>x . Label I '''' 0" -- Labelling
  apply(unfold_locales) 
      apply(auto)
     apply(simp add: Transitive_Closure.refl_rtrancl)
    apply(metis Domain_empty Domain_insert Not_Domain_rtrancl antisym_def singletonD)
   apply(simp add: Transitive_Closure.trans_rtrancl)
  apply(simp add: sym_def)
  done
      
thm labelledES.well_justified_def
thm labelledES.config_domain_def
thm mem_Collect_eq[where P="\<lambda>C . emptyES.conflict_free C \<and> emptyES.down_closed C"]
  
lemma (in labelledES) "emptyES.well_justified {}"
  apply(simp only: emptyES.well_justified_def)
  apply (rule conjI)
  using emptyES.justified_def apply blast
  apply(rule conjI)
   apply(simp only: emptyES.config_domain_def)
   apply(simp only: mem_Collect_eq)
   apply(auto simp only: emptyES.conflict_free_def)
   apply(auto simp only: emptyES.down_closed_def)
   apply(simp only: emptyES.ae_justifies_subset_star_def)
  done
    (*
    theorem emptyESValidES: "isValidES"
      apply(auto simp add: isValidES_def initialES_def isValidPO_def minimal_def isConfValid_def)
      apply(rule refl_Id)
         apply(rule trans_Id)
        apply(rule antisym_Id)
       apply(simp add: symmetriccl_def symmetric_symmetriccl)
       apply(simp add: sym_def trans_def irrefl_def)
      apply(simp add: trans_rtrancl)
      done
        
    lemma initialConfig_no_read: "\<not> is_read x"
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
    *)
  end
end
  