theory EventStructures
imports Main Enum String 
begin

class event_structure =
  fixes event_set :: "'a::ord set"
  fixes partial_order :: "'a \<Rightarrow> 'a \<Rightarrow> bool" (infix "''\<le>''" 50)
  fixes conflict :: "'a \<Rightarrow> 'a \<Rightarrow> bool" (infix "''\<bowtie>''" 50)
  fixes labelling :: "'a \<Rightarrow> label"

  assumes partial_order_refl: "x \<le> x"
  assumes partial_order_trans: "x \<le> y \<Longrightarrow> y \<le> z \<Longrightarrow> x \<le> z"
  assumes partial_order_antisym: "x \<le> y \<Longrightarrow> y \<le> x \<Longrightarrow> x = y"  

  assumes conflict_sym: "x '\<bowtie>' y \<Longrightarrow> y '\<bowtie>' x"
  assumes conflict_trans: "x '\<bowtie>' y \<Longrightarrow> y '\<bowtie>' z \<Longrightarrow> x '\<bowtie>' z"
  assumes conflict_over_order: "(x '\<bowtie>' y) \<and> (y \<le> z) \<Longrightarrow> x '\<bowtie>' z"
  (*primitive conflict constraint*)
  assumes conflict_minimal: "((d '\<bowtie>' e) \<and> (b \<le> d) \<and> (b '\<bowtie>' c) \<and> (c \<le> e)) \<Longrightarrow> (d = b \<and> c = e)"

datatype mem_action = W | R | I | N
(*record label =
  action :: "mem_action"
  location :: string
  val :: int*)

datatype label = Label mem_action string int

(*Prime Event Structure with below restrictions*)
record 'a event_structure_data =
  event_set :: "'a set"
  partial_order :: "'a \<Rightarrow> 'a \<Rightarrow> bool"
  primitive_conflict :: "'a \<Rightarrow> 'a \<Rightarrow> bool"
  label_function :: "'a \<Rightarrow> label"

definition refl :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> bool" where
"refl po \<equiv> (\<forall>x. po x x \<longrightarrow> True)"

definition trans :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> bool" where
"trans po \<equiv> (\<forall>x.\<forall>y.\<forall>z. (po x y \<and> po y z) \<longrightarrow> po x z)"

definition antisym :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> bool" where
"antisym po \<equiv> (\<forall>x.\<forall>y. (po x y \<and> po y x) \<longrightarrow> x = y)"

definition isValidPO :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> bool" where
"isValidPO po \<equiv> (
  refl po \<and> 
  trans po \<and> 
  antisym po
)"

definition symmetric :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> bool" where
"symmetric conf \<equiv> (\<forall>x.\<forall>y. conf x y \<longrightarrow> conf y x)" 

definition isConfValid :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> bool" where
"isConfValid conf \<equiv> (
  symmetric conf \<and> 
  trans conf
)"

definition confOverPO :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> bool" where
"confOverPO po conf \<equiv> (\<forall>x.\<forall>y.\<forall>z. (conf x y \<and> po y z) \<longrightarrow> conf x z)"

(*Minimal/Primitive conflict condition*)
definition minimal :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> bool" where
"minimal po conf \<equiv> 
  (\<forall>w.\<forall>x.\<forall>y.\<forall>z. (conf y z \<and> po x y \<and> conf x w \<and> po w z \<longrightarrow> (y = x) \<and> (w = z)))"

definition isValid :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> bool" where
"isValid po conf \<equiv> (
  minimal po conf \<and> 
  confOverPO po conf \<and> 
  isConfValid conf \<and> 
  isValidPO po
)"

definition isValidES :: "'a event_structure_data \<Rightarrow> bool" where
"isValidES es == isValid (partial_order es) (primitive_conflict es)" 

value "True = False"

fun justifies_event :: "label \<Rightarrow> label \<Rightarrow> bool" where
"justifies_event (Label I l v) (Label R l2 v2) = ((l = l2) \<and> (v = 0))"|
"justifies_event (Label W l v) (Label R l2 v2) = ((l = l2) \<and> (v = v2))"|
"justifies_event x y = False"

(*
record 'a configuration = 
  event_set :: "'a set"
  order :: "'a \<Rightarrow> 'a \<Rightarrow> bool"
  label_fn :: "'a \<Rightarrow> label"*)

value "(Label W ''x'' 2)"

definition conflict_free :: "'a set \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> bool" where
"conflict_free events conf \<equiv> (\<forall>e\<in>events. \<not>(\<exists>f\<in>events. conf e f))"

fun getMemAction :: "label \<Rightarrow> mem_action" where
"getMemAction (Label I l v) = I"|
"getMemAction (Label W l v) = W"|
"getMemAction (Label R l v) = R"

(*is this correct?*)
definition down_closure :: "'a set \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> label) \<Rightarrow> bool" where
"down_closure events order labelfn \<equiv> (\<forall>e\<in>events. \<exists>f\<in>events. 
  (order f e) \<or> ((getMemAction (labelfn e)) = I))"

definition justifies_config :: "'a event_structure_data \<Rightarrow> 'a event_structure_data \<Rightarrow> bool" where
"justifies_config es1 es2 \<equiv>
 (\<forall>x\<in>(event_set es2). \<exists>y\<in>(event_set es1). (justifies_event (label_function es1 y) (label_function es2 x)))"

definition ae_justifies :: "'a event_structure_data \<Rightarrow> 'a event_structure_data \<Rightarrow> bool" where
"ae_justifies es1 es2 \<equiv>
  \<forall>c. justifies_config es1 c \<longrightarrow> (\<exists>d.(justifies_config c d \<and> justifies_config d es2))"

value "{}"
value "\<lambda>(x,y).False"

definition empty_ES :: "int event_structure_data" where
"empty_ES \<equiv> 
  \<lparr> event_set = {},
  partial_order = \<lambda>x y. False,
  primitive_conflict = \<lambda>x y. False,
  label_function = \<lambda>x.(Label N '''' 0) \<rparr>"

(*well justification when \<emptyset> justifies C*)
definition well_justified :: "'a event_structure_data \<Rightarrow> bool" where
"well_justified es \<equiv> ae_justifies empty_ES es"

end