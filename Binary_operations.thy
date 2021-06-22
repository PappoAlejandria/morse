theory Binary_operations
 imports Bij_betw_simplicial_complex_bool_func
begin

definition bool_fun_or :: "(bool^'n \<Rightarrow> bool) \<Rightarrow> (bool^'n \<Rightarrow> bool) \<Rightarrow> (bool^'n \<Rightarrow> bool)"
  where "(bool_fun_or f g) x \<equiv> (f x) \<or> (g x)"

definition bool_fun_and :: "(bool^'n \<Rightarrow> bool) \<Rightarrow> (bool^'n \<Rightarrow> bool) \<Rightarrow> (bool^'n \<Rightarrow> bool)"
  where "(bool_fun_and f g) x \<equiv> (f x) \<and> (g x)"

definition bool_fun_ast :: "(bool^'n \<Rightarrow> bool) \<Rightarrow> (bool^'m \<Rightarrow> bool) \<Rightarrow> (bool^'n \<Rightarrow> bool^'m \<Rightarrow> bool)"
  where "(bool_fun_ast f g) x y \<equiv> (f x) \<and> (g y)"

definition set_ast :: "('a set) \<Rightarrow> ('a set) \<Rightarrow> ('a set)"
  where "set_ast A B = {}"

lemma eq_union_or: 
"simplicial_complex_induced_by_monotone_boolean_function (bool_fun_or f g)
= simplicial_complex_induced_by_monotone_boolean_function f \<union> simplicial_complex_induced_by_monotone_boolean_function g"
proof
  show "simplicial_complex_induced_by_monotone_boolean_function f \<union> simplicial_complex_induced_by_monotone_boolean_function g \<subseteq> simplicial_complex_induced_by_monotone_boolean_function (bool_fun_or f g)"
  proof
    fix \<sigma>::"'a set"
    assume "\<sigma> \<in> simplicial_complex_induced_by_monotone_boolean_function f \<union> simplicial_complex_induced_by_monotone_boolean_function g"
    hence "\<sigma> \<in> simplicial_complex_induced_by_monotone_boolean_function f \<or> \<sigma> \<in> simplicial_complex_induced_by_monotone_boolean_function g"
      by auto
    hence "f (bool_vec_from_simplice \<sigma>) \<or> g (bool_vec_from_simplice \<sigma>)"
      by (metis (mono_tags, lifting) bool_vec_set_from_simplice_set_def boolean_function_from_simplicial_complex_def boolean_function_from_simplicial_complex_simplicial_complex_induced_by_monotone_boolean_function_id mem_Collect_eq)
    hence "bool_fun_or f g (bool_vec_from_simplice \<sigma>)"
      unfolding bool_fun_or_def
      by auto
    thus "\<sigma> \<in> simplicial_complex_induced_by_monotone_boolean_function (bool_fun_or f g)"
      using simplicial_complex_induced_by_monotone_boolean_function_def
      by fastforce
  qed
next
  show "simplicial_complex_induced_by_monotone_boolean_function (bool_fun_or f g) \<subseteq> simplicial_complex_induced_by_monotone_boolean_function f \<union> simplicial_complex_induced_by_monotone_boolean_function g"
  proof
    fix \<sigma>::"'a set"
    assume sigma: "\<sigma> \<in> simplicial_complex_induced_by_monotone_boolean_function (bool_fun_or f g)"
    hence "bool_fun_or f g (bool_vec_from_simplice \<sigma>)"
      by (metis (mono_tags, lifting) bool_vec_set_from_simplice_set_def boolean_function_from_simplicial_complex_def boolean_function_from_simplicial_complex_simplicial_complex_induced_by_monotone_boolean_function_id mem_Collect_eq)
    hence "(f (bool_vec_from_simplice \<sigma>)) \<or> (g (bool_vec_from_simplice \<sigma>))"
      unfolding bool_fun_or_def
      by auto
    hence "\<sigma> \<in> simplicial_complex_induced_by_monotone_boolean_function f \<or> \<sigma> \<in> simplicial_complex_induced_by_monotone_boolean_function g"
      by (smt (z3) sigma bool_fun_or_def mem_Collect_eq simplicial_complex_induced_by_monotone_boolean_function_def)
    thus "\<sigma> \<in> simplicial_complex_induced_by_monotone_boolean_function f \<union> simplicial_complex_induced_by_monotone_boolean_function g"
      by auto
  qed
qed

lemma eq_inter_and: 
"simplicial_complex_induced_by_monotone_boolean_function (bool_fun_and f g)
= simplicial_complex_induced_by_monotone_boolean_function f \<inter> simplicial_complex_induced_by_monotone_boolean_function g"
proof
  show "simplicial_complex_induced_by_monotone_boolean_function f \<inter> simplicial_complex_induced_by_monotone_boolean_function g \<subseteq> simplicial_complex_induced_by_monotone_boolean_function (bool_fun_and f g)"
  proof
    fix \<sigma>::"'a set"
    assume "\<sigma> \<in> simplicial_complex_induced_by_monotone_boolean_function f \<inter> simplicial_complex_induced_by_monotone_boolean_function g"
    hence "\<sigma> \<in> simplicial_complex_induced_by_monotone_boolean_function f \<and> \<sigma> \<in> simplicial_complex_induced_by_monotone_boolean_function g"
      by auto
    hence "f (bool_vec_from_simplice \<sigma>) \<and> g (bool_vec_from_simplice \<sigma>)"
      by (metis (mono_tags, lifting) bool_vec_set_from_simplice_set_def boolean_function_from_simplicial_complex_def boolean_function_from_simplicial_complex_simplicial_complex_induced_by_monotone_boolean_function_id mem_Collect_eq)
    hence "bool_fun_and f g (bool_vec_from_simplice \<sigma>)"
      unfolding bool_fun_and_def
      by auto
    thus "\<sigma> \<in> simplicial_complex_induced_by_monotone_boolean_function (bool_fun_and f g)"
      using simplicial_complex_induced_by_monotone_boolean_function_def
      by fastforce
  qed
next
  show "simplicial_complex_induced_by_monotone_boolean_function (bool_fun_and f g) \<subseteq> simplicial_complex_induced_by_monotone_boolean_function f \<inter> simplicial_complex_induced_by_monotone_boolean_function g"
  proof
    fix \<sigma>::"'a set"
    assume sigma: "\<sigma> \<in> simplicial_complex_induced_by_monotone_boolean_function (bool_fun_and f g)"
    hence "bool_fun_and f g (bool_vec_from_simplice \<sigma>)"
      by (metis (mono_tags, lifting) bool_vec_set_from_simplice_set_def boolean_function_from_simplicial_complex_def boolean_function_from_simplicial_complex_simplicial_complex_induced_by_monotone_boolean_function_id mem_Collect_eq)
    hence "(f (bool_vec_from_simplice \<sigma>)) \<and> (g (bool_vec_from_simplice \<sigma>))"
      unfolding bool_fun_and_def
      by auto
    hence "\<sigma> \<in> simplicial_complex_induced_by_monotone_boolean_function f \<and> \<sigma> \<in> simplicial_complex_induced_by_monotone_boolean_function g"
      by (smt (z3) sigma bool_fun_and_def mem_Collect_eq simplicial_complex_induced_by_monotone_boolean_function_def)
    thus "\<sigma> \<in> simplicial_complex_induced_by_monotone_boolean_function f \<inter> simplicial_complex_induced_by_monotone_boolean_function g"
      by auto
  qed
qed

end