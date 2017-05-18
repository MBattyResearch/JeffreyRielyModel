section {* Model *}
text {* This is an implementation of Alan Jeffrey's Event Structure Memory Model in Isabelle/HOL. *}
  
theory EventStructures
imports Main Relation Transitive_Closure RelationalLemmas EventStructures2
begin
  
(*text{* Primitive conflict has no edges in it which can be inferred by the rule 
@{thm [source] confOverPO_def}. *}
definition minimal :: "event rel \<Rightarrow> event rel \<Rightarrow> bool" where
"minimal po conf \<equiv> 
  (\<forall>w.\<forall>x.\<forall>y.\<forall>z. 
    ((y, z) \<in> conf \<and> 
     (x, y) \<in> po \<and> 
     (x, w) \<in> conf \<and>
     (w, z) \<in> po \<longrightarrow> (y = x) \<and> (w = z)))"
*)

(*
text{* Valid event structures are finite, have valid @{term primitive_order}, and valid 
@{term primitive_conflict} *}
definition isValid :: "event set \<Rightarrow> event rel  \<Rightarrow> event rel \<Rightarrow> bool" where
"isValid es po conf \<equiv> (
  finite es \<and>
  isValidPO es po \<and>
  minimal po conf \<and> 
  isConfValid conf
)"


declare isValid_def [simp]

definition isValidES :: "event event_structure \<Rightarrow> bool" where
-- {* Need symmetric closure of primitive conflict *}
"isValidES es \<equiv> isValid 
  (event_set es)
  ((primitive_order es)\<^sup>* )
  ((symmetriccl (primitive_conflict es))\<^sup>+ - Id)"
*)

fun justifies_event :: "label \<Rightarrow> label \<Rightarrow> bool" where
"justifies_event (Label I '''' v) (Label R l2 v2) = (v2 = 0)"|
"justifies_event (Label W l v) (Label R l2 v2) = ((l = l2) \<and> (v = v2))"|
(*"justifies_event x (Label W l v) = True"|
"justifies_event x (Label I l v) = True"|*)
"justifies_event x y = False"



(*Helper function to get the type of memory action from an event label*)
fun getMemAction :: "label \<Rightarrow> mem_action" where
"getMemAction (Label x _ _) = x"

print_locale labelledES

context labelledES
  begin     
    (*All read events in a configuration are justified by an event in that configuration*)
    definition justified :: "event config \<Rightarrow> bool" where
      "justified c \<equiv> (\<forall>r\<in> c. (getMemAction (label r) = R) \<longrightarrow> 
        (\<exists>e\<in>c. (justifies_event (label e) (label r))))"
    
    definition prec :: "event \<Rightarrow> event \<Rightarrow> bool" (infixl "\<preceq>" 50) where 
      "prec x y \<equiv> (x, y) \<in> preceeds"
    declare prec_def[simp]
  
    definition conf :: "event \<Rightarrow> event \<Rightarrow> bool" ("#" 50) where
      "conf x y \<equiv> (x, y) \<in> conflict"
      
    definition conflict_free :: "event config \<Rightarrow> bool" where
      "conflict_free C \<equiv> \<forall>x y. x \<in> C \<and> y \<in> C \<longrightarrow> \<not> conf x y"
      
    definition down_closed :: "event config \<Rightarrow> bool" where
      "down_closed C \<equiv> \<forall>x y . x \<in> C \<and> y \<preceq> x \<longrightarrow> y \<in> C"
    
    definition is_read :: "event \<Rightarrow> bool" where
      "is_read x \<equiv> (getMemAction (label x) = R)"

    definition justifies_config :: "event config \<Rightarrow> event config \<Rightarrow> bool"  where
      "justifies_config A B \<equiv> \<forall>x \<in> B. is_read x \<longrightarrow> (\<exists>y \<in> A. justifies_event (label y) (label x))"

    definition justifies_config_subset :: "event config \<Rightarrow> event config \<Rightarrow> bool" (infixl "\<lesssim>" 60) where
      "justifies_config_subset A B  \<equiv> A \<subseteq> B \<and> justifies_config A B"

    definition justifies_config_star ::  "event config \<Rightarrow> event config \<Rightarrow> bool" (infixl "\<lesssim>\<^sup>*" 60) where
      "justifies_config_star a b \<equiv> justifies_config_subset\<^sup>*\<^sup>* a b"
      
    definition config_domain :: "event config set" ("\<CC>") where
      "config_domain \<equiv> {C . conflict_free C \<and> down_closed C}"       
        
    definition ae_justifies :: "event config  \<Rightarrow> event config \<Rightarrow> bool" where
      "ae_justifies C D \<equiv> \<forall>C' \<in> \<CC>. (C \<lesssim>\<^sup>* C') \<longrightarrow> (\<exists>C'' \<in> \<CC>. (C' \<lesssim>\<^sup>* C'') \<and> justifies_config C'' D)"
      
    definition ae_justifies_subset :: "event config \<Rightarrow> event config \<Rightarrow> bool" (infixl "\<sqsubseteq>" 60) where
      "ae_justifies_subset C D \<equiv> C \<subseteq> D \<and> ae_justifies C D"
    
    definition ae_justifies_subset_star :: "event config \<Rightarrow> event config \<Rightarrow> bool" (infixl "\<sqsubseteq>\<^sup>*" 60) where
      "ae_justifies_subset_star C D \<equiv> ae_justifies_subset\<^sup>*\<^sup>* C D"
    
    definition well_justified :: "event config  \<Rightarrow> bool" where
      "well_justified C \<equiv> (justified C) \<and> C \<in> \<CC> \<and> {}\<sqsubseteq>\<^sup>*C"
    
    definition initialConfig :: "event set" ("\<C>" 1000) where
      "initialConfig \<equiv> {}"
                                         
    declare initialConfig_def [simp]
  end
end