section {* Model *}
text {* This is an implementation of Alan Jeffrey's Event Structure Memory Model in Isabelle/HOL. *}
theory EventStructuresRelational
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
(*Prime Event Structure with below restrictions*)
record 'a event_structure_data =
  event_set :: "'a set"
  primitive_order :: "'a rel"
  primitive_conflict :: "'a rel"
  label_function :: "'a \<Rightarrow> label"
  
text{* A valid program order is reflexive, transitive and antisymmetric. *}
definition isValidPO :: "'a set \<Rightarrow> 'a rel \<Rightarrow> bool" where
"isValidPO es po \<equiv> (
  refl po \<and> 
  trans po \<and> 
  antisym po
)"

definition symmetric:: "'a rel \<Rightarrow> bool" where
  "symmetric r \<equiv> \<forall>x y . (x, y) \<in> r \<longrightarrow> (y, x) \<in> r"

text{* A valid conflict relation is symetric and transitive. *}
definition isConfValid :: "'a rel \<Rightarrow> bool" where
"isConfValid conf \<equiv> (
  symmetric conf \<and> 
  trans conf
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
declare minimal_def [simp]
declare isConfValid_def [simp]

definition isValidES :: "'a event_structure_data \<Rightarrow> bool" where
"isValidES es \<equiv> isValid 
  (event_set es)
  ((primitive_order es)\<^sup>*)
  ((primitive_conflict es)\<^sup>*)"

fun justifies_event :: "label \<Rightarrow> label \<Rightarrow> bool" where
"justifies_event (Label I '''' v) (Label R l2 v2) = (v2 = 0)"|
"justifies_event (Label W l v) (Label R l2 v2) = ((l = l2) \<and> (v = v2))"|
"justifies_event x (Label W l v) = True"|
"justifies_event x (Label I l v) = True"|
"justifies_event x y = False"

definition conflict_free :: "'a config \<Rightarrow> 'a rel \<Rightarrow> bool" where
"conflict_free c conf \<equiv> (\<forall>e\<in>c. \<not>(\<exists>f\<in>c. (e, f) \<in> conf))"

(*Helper function to get the type of memory action from an event label*)
fun getMemAction :: "label \<Rightarrow> mem_action" where
"getMemAction (Label I l v) = I"|
"getMemAction (Label W l v) = W"|
"getMemAction (Label R l v) = R"

(*is this correct?*)
definition down_closure :: "'a set \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> label) \<Rightarrow> bool" where
"down_closure events order labelfn \<equiv> (\<forall>e\<in>events. \<exists>f\<in>events. 
  (order f e) \<or> ((getMemAction (labelfn e)) = I))"

(*All read events in a configuration are justified by an event in that configuration*)
definition justified :: "'a event_structure_data \<Rightarrow> 'a config \<Rightarrow> bool" where
"justified es c \<equiv>
   (\<forall>r\<in> c. (getMemAction (label_function es r) = R) \<longrightarrow> 
    (\<exists>e\<in>c. (justifies_event (label_function es e) (label_function es r))))"


definition justifies_config :: "'a event_structure_data \<Rightarrow> 'a config rel" where
  "justifies_config es \<equiv> 
    { (c\<^sub>1, c\<^sub>2) . 
      \<forall>x \<in> c\<^sub>2. 
        \<exists>y \<in> c\<^sub>1 . (justifies_event (label_function es y) (label_function es x)) }"

definition ae_justifies :: "'a event_structure_data \<Rightarrow> 'a config \<Rightarrow> 'a config \<Rightarrow> bool" where
  "ae_justifies es c\<^sub>1 c\<^sub>2 \<equiv>
    \<forall>x. ((x, c\<^sub>1) \<in> ((justifies_config es)\<^sup>*)) \<longrightarrow>
      (\<exists>y. ((x, y) \<in> ((justifies_config es)\<^sup>*)) \<and>
        ((y, c\<^sub>2) \<in> (justifies_config es)))"
  
definition empty_ES :: "string event_structure_data" where
"empty_ES \<equiv> \<lparr> 
  event_set = {''a''},
  primitive_order ={},
  primitive_conflict = {},
  label_function = \<lambda>x.(Label I '''' 0)
\<rparr>"

definition subset_AE_justifies :: "'a event_structure_data \<Rightarrow> ('a config) rel" where
"subset_AE_justifies es \<equiv> {(c\<^sub>1, c\<^sub>2) . (c\<^sub>1 \<subseteq> c\<^sub>2) \<and> (ae_justifies es c\<^sub>1 c\<^sub>2)}"

definition well_justified :: "'a event_structure_data \<Rightarrow> 'a config  \<Rightarrow> bool" where
"well_justified es c \<equiv> 
  (isValidES es) \<and> 
  (justified es c) \<and> 
  ({}, c) \<in> ((subset_AE_justifies es)\<^sup>*)"
end