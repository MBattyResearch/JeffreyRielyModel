theory ESProperties
imports EventStructures ExampleEventStructures String EventStructures2
begin


context labelledES
begin
    
  lemma ae_justifies_refl[simp]: "C \<lesssim>\<^sup>* C"
    apply(simp add: justifies_config_star_def)
    done
  
  lemma aej_subset: "C \<lesssim>\<^sup>* D \<Longrightarrow> C \<subseteq> D"
    apply(simp only: justifies_config_star_def)
    apply(rule rtranclp_induct[where a=C, where b=D, where r="justifies_config_subset", 
          where P="\<lambda>x . C \<subseteq> x"])
      apply(auto simp add: justifies_config_subset_def)
    done
      
  lemma ref_impl: "C \<lesssim>C' \<Longrightarrow> C' \<lesssim> C'"
    apply(simp add: justifies_config_subset_def  justifies_config_def)
    apply clarsimp
    apply blast
    done
        
  lemma add_write_okay: "C' \<lesssim> C' \<Longrightarrow> \<not>(is_read ev) \<Longrightarrow> C' \<lesssim> C' \<union> {ev}"
    apply(simp only: justifies_config_subset_def justifies_config_def)
    apply(simp (no_asm) add: justifies_config_subset_def justifies_config_def)
    apply auto
    done 
      
  lemma add_write_really_okay: "C \<lesssim> C' \<Longrightarrow> \<not>(is_read ev) \<Longrightarrow> C' \<lesssim> C' \<union> {ev}"
    apply(rule add_write_okay)
    apply(rule ref_impl)
     apply assumption+
    done
  
  lemma just_in_rjuststar: "C \<lesssim> C' \<Longrightarrow> C \<lesssim>\<^sup>* C'"
    apply(simp add: justifies_config_star_def)
    done
  
  lemma add_write_super_okay: "C \<lesssim> C' \<Longrightarrow> \<not>(is_read ev) \<Longrightarrow> C \<lesssim>\<^sup>* C' \<union> {ev}"
    apply(rule just_in_rjuststar)
    apply(simp only: justifies_config_subset_def)
    apply(simp only: justifies_config_def)
    apply auto
    done 
      
  
  lemma just_config_imp_round: "justifies_config C D \<Longrightarrow> C \<lesssim>\<^sup>* C' \<Longrightarrow> (\<exists>C'' . C' \<lesssim>\<^sup>* C'' \<longrightarrow>  justifies_config C'' D)"
    apply(rule exI)
    apply(rule impI)
    apply(frule ae_justifies_refl)
    done
      
  -- {* For every step of adding something to C' we have that the previous steps are included, so any
        "dependants" remain.
        Mark: in the final step (C_0,C') , all reads in C' are justified by C_0, and C_0 is a subset,
        so all reads in C' are justified by writes in C'. *}
  lemma aejrefl_and_aejstar_imp_aej: "C \<lesssim> C \<Longrightarrow> C \<lesssim>\<^sup>* C' \<Longrightarrow> C' \<lesssim> C'"
    apply(simp add: justifies_config_star_def)
    apply(simp add: rtranclp_eq_Id_trancl)
      apply(erule disjE)
     apply(simp_all)
    apply(simp add: tranclp_unfold_right)
    apply(simp add: justifies_config_subset_def justifies_config_def)
    apply clarsimp
    apply(rename_tac "C\<^sub>0")
    apply(simp add: justifies_config_def justifies_config_subset_def)
    apply blast
    done

  theorem emptyESJustEmptyES: "{} \<lesssim> {}"
    apply(auto simp add: justifies_config_def justifies_config_subset_def)
    done
  
value \<C>

thm aejrefl_and_aejstar_imp_aej[where C="{}"]

  lemma just_star_imp_just: "{} \<lesssim>\<^sup>* C' \<Longrightarrow> C' \<lesssim> C'"
    apply(rule aejrefl_and_aejstar_imp_aej)
    apply(simp add: justifies_config_star_def justifies_config_def)
     apply(rule emptyESJustEmptyES)
    apply(assumption)
    done
      
  lemma just_config_star_split: "A \<lesssim> B \<Longrightarrow> B \<lesssim> C \<Longrightarrow> A \<lesssim>\<^sup>* C"
    apply(simp add: justifies_config_star_def justifies_config_def)
    done
  
  lemma just_config_star_splitL: "A \<lesssim>\<^sup>* B \<Longrightarrow> B \<lesssim> C \<Longrightarrow> A \<lesssim>\<^sup>* C"    
    apply(simp add: justifies_config_star_def justifies_config_def)
    done
      
  lemma just_config_star_splitR: "A \<lesssim> B \<Longrightarrow> B \<lesssim>\<^sup>* C \<Longrightarrow> A \<lesssim>\<^sup>* C"    
    apply(simp add: justifies_config_star_def justifies_config_def)
    done

  end
end
