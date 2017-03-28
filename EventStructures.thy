section {* Model *}
text {* This is an implementation of Alan Jeffrey's Event Structure Memory Model in Isabelle/HOL. *}
  
theory EventStructures
imports Main Relation Transitive_Closure
begin
  
subsection{* Basic Definitions *}
text{* There are 3 types of event in the system, Writes, Reads and the Initialisation. *}
datatype mem_action = W | R | I 
(*Memory action, location, value*)
  
text{* Labels are comprised of an event, a location and a value. *}
datatype label = Label mem_action string int

text{*Configurations are sets of events. *}
type_synonym 'a config = "'a set"

text{*Event Structures are sets of events, and relations on those events. Specificically 
@{term primitive_order}, which is the transitive reduction of the order relation, and 
@{term primitive_conflict} which when symmetrically, reflexively closed builds the full primitive
conflict relation as described in the paper.*}
(*Prime Event Structure with bt selow restrictions*)
record 'a event_structure =
  event_set :: "'a set"
  primitive_order :: "'a rel"
  primitive_conflict :: "'a rel"
  label_function :: "'a \<Rightarrow> label"
  
text{* A valid program order is reflexive, transitive and antisymmetric. *}
definition isValidPO :: "'a set \<Rightarrow> 'a rel \<Rightarrow> bool" where
"isValidPO evs po \<equiv> (
  refl po \<and> 
  trans po \<and> 
  antisym po
)"

definition symmetric:: "'a rel \<Rightarrow> bool" where
  "symmetric r \<equiv> \<forall>a b . (a, b) \<in> r \<longleftrightarrow> (b, a) \<in> r"

definition symmetriccl:: "'a rel \<Rightarrow> 'a rel" where
  "symmetriccl r \<equiv> {(y, x) . (x, y) \<in> r} \<union> r"
  
lemma symmetric_symmetriccl: "\<forall>r . symmetric (symmetriccl r)"
  apply(simp add: symmetric_def symmetriccl_def)
  by auto    
  
text{* A valid conflict relation is symetric and transitive. *}
-- {* Should this be minus reflexive edges too? Mark is suspicious *}
definition isConfValid :: "'a rel \<Rightarrow> bool" where
"isConfValid conf \<equiv> (
  symmetric conf \<and>
  trans (conf \<union> Id) \<and>
  irrefl conf
)"

text{* Conflict transits through program order. *}
definition confOverPO :: "'a rel \<Rightarrow> 'a rel \<Rightarrow> bool" where
"confOverPO po conf \<equiv> (\<forall>x.\<forall>y.\<forall>z. ((x, y) \<in> conf \<and> (y, z) \<in> po) \<longrightarrow> (x, z) \<in> conf)"

text{* Primitive conflict has no edges in it which can be infered by the rule 
@{thm [source] confOverPO_def}. *}
definition minimal :: "'a rel \<Rightarrow> 'a rel \<Rightarrow> bool" where
"minimal po conf \<equiv> 
  (\<forall>w.\<forall>x.\<forall>y.\<forall>z. 
    ((y, z) \<in> conf \<and> 
     (x, y) \<in> po \<and> 
     (x, w) \<in> conf \<and>
     (w, z) \<in> po \<longrightarrow> (y = x) \<and> (w = z)))"

text{* Valid event structures are finite, have valid @{term primitive_order}, and valid 
@{term primitive_conflict} *}
definition isValid :: "'a set \<Rightarrow> 'a rel  \<Rightarrow> 'a rel \<Rightarrow> bool" where
"isValid es po conf \<equiv> (
  finite es \<and>
  isValidPO es po \<and>
  minimal po conf \<and> 
  isConfValid conf
)"

declare isValid_def [simp]

definition isValidES :: "'a event_structure \<Rightarrow> bool" where
-- {* Need symmetric closure of primitive conflict *}
"isValidES es \<equiv> isValid 
  (event_set es)
  ((primitive_order es)\<^sup>*)
  ((symmetriccl (primitive_conflict es))\<^sup>+ - Id)"

(* FIXME 
function justifies_event :: "label set \<Rightarrow> label rel" where
"justifies_event evs \<equiv> 
  { (w, r) . (w \<in> evs) \<and> (r \<in> evs) \<and> (\<exists>l l2 v v2 . ((w = (Label W l v)) \<and> (r = (Label R l2 v2)) \<and> (l = l2) \<and> (v = v2))) } \<union>
  { (i, r) . (i \<in> evs) \<and> (r \<in> evs) \<and> (\<exists>v . (i = (Label I '''' _)) \<and> (r = (Label R _ v)) \<and> (v = 0))}"
*)
fun justifies_event :: "label \<Rightarrow> label \<Rightarrow> bool" where
"justifies_event (Label I '''' v) (Label R l2 v2) = (v2 = 0)"|
"justifies_event (Label W l v) (Label R l2 v2) = ((l = l2) \<and> (v = v2))"|
(*"justifies_event x (Label W l v) = True"|
"justifies_event x (Label I l v) = True"|*)
"justifies_event x y = False"

definition conflict_free :: "'a config \<Rightarrow> 'a rel \<Rightarrow> bool" where
"conflict_free c conf \<equiv> (\<forall>e\<in>c. \<not>(\<exists>f\<in>c. (e, f) \<in> conf))"

(*Helper function to get the type of memory action from an event label*)
fun getMemAction :: "label \<Rightarrow> mem_action" where
"getMemAction (Label x _ _) = x"

(*is this correct?*)
(* 'a set \<Rightarrow> 'a event_structure \<Rightarrow> bool *)
(* Note that this is primitive_order\<^sup>+ rather than primitive_order\<^sup>* because we do not want the 
   reflexive edges when checking for down_closure *)
definition down_closure :: "'a set \<Rightarrow> 'a event_structure \<Rightarrow> bool" where
"down_closure events ev_s \<equiv> (\<forall>e\<in>events. \<exists>f\<in>events. 
  ((f, e) \<in> ((primitive_order ev_s)\<^sup>+)) \<or> ((getMemAction (label_function ev_s e)) = I))"

(*All read events in a configuration are justified by an event in that configuration*)
definition justified :: "'a event_structure \<Rightarrow> 'a config \<Rightarrow> bool" where
"justified es c \<equiv>
   (\<forall>r\<in> c. (getMemAction (label_function es r) = R) \<longrightarrow> 
    (\<exists>e\<in>c. (justifies_event (label_function es e) (label_function es r))))"

definition justifies_config :: "'a event_structure \<Rightarrow> 'a config rel" where
  "justifies_config es \<equiv> 
    { (c\<^sub>1, c\<^sub>2) . \<forall>x \<in> c\<^sub>2. \<exists>y \<in> c\<^sub>1. (c\<^sub>1 \<subseteq> c\<^sub>2) \<and> 
      (getMemAction (label_function es x) = R) \<and>
      ((getMemAction (label_function es y) = W) \<or> (getMemAction (label_function es y) = I)) \<and>
      (justifies_event (label_function es y) (label_function es x)) }"

definition justifies_config_inf:: "'a config \<Rightarrow> 'a event_structure \<Rightarrow> 'a config \<Rightarrow> bool" ("_ \<lesssim>\<^bsub>_\<^esub> _" [61,60,60] 60) where
  "justifies_config_inf a es b \<equiv> (a, b) \<in> (justifies_config es)"

definition justifies_config_star_inf::  "'a config \<Rightarrow> 'a event_structure \<Rightarrow> 'a config \<Rightarrow> bool" ("_ \<lesssim>\<^sup>*\<^bsub>_\<^esub> _" [61,60,60] 60) where
    "justifies_config_star_inf a es b \<equiv> (a, b) \<in> (justifies_config es)\<^sup>*"
  
definition ae_justifies :: "'a config \<Rightarrow>'a event_structure \<Rightarrow> 'a config \<Rightarrow> bool" ("_ \<sqsubseteq>\<^bsub>_\<^esub> _" [61,60,60] 60)where
  "ae_justifies C es D \<equiv> \<forall>C'. (C\<lesssim>\<^sup>*\<^bsub>es\<^esub>C') \<longrightarrow> 
    (\<exists>C''. (C'\<lesssim>\<^sup>*\<^bsub>es\<^esub> C'') \<and> (C''\<lesssim>\<^bsub>es\<^esub> D))"

definition ae_justifies_star :: "'a config \<Rightarrow> 'a event_structure \<Rightarrow> 'a config \<Rightarrow> bool" ("_ \<sqsubseteq>\<^sup>*\<^bsub>_\<^esub> _" [61,60,60] 60) where
"ae_justifies_star a es b \<equiv> (a, b) \<in> {(c\<^sub>1, c\<^sub>2) . (c\<^sub>1 \<subseteq> c\<^sub>2) \<and> (c\<^sub>1 \<sqsubseteq>\<^bsub>es\<^esub> c\<^sub>2)}\<^sup>*"

definition well_justified :: "'a event_structure \<Rightarrow> 'a config  \<Rightarrow> bool" where
"well_justified es C \<equiv> 
  (isValidES es) \<and> (justified es C) \<and> 
  {}\<sqsubseteq>\<^sup>*\<^bsub>es\<^esub>C"

definition empty_ES :: "string event_structure" where
"empty_ES \<equiv> \<lparr> 
  event_set = {},
  primitive_order ={},
  primitive_conflict = {},
  label_function = \<lambda>x.(Label I '''' 0)
\<rparr>"

end