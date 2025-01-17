
text\<open>
  Author: Julius Michaelis
\<close>

theory MkIfex
  imports "ROBDD.BDT"
begin

fun mk_ifex :: "('a :: linorder) boolfunc \<Rightarrow> 'a list \<Rightarrow> 'a ifex" where
"mk_ifex f [] = (if f (const False) then Trueif else Falseif)" |
"mk_ifex f (v#vs) = ifex_ite (IF v Trueif Falseif) (mk_ifex (bf_restrict v True f) vs) (mk_ifex (bf_restrict v False f) vs)"

lemma mk_ifex_ro: "ro_ifex (mk_ifex f vs)"
  by(induction vs arbitrary: f; fastforce intro: order_ifex_ite_invar minimal_ifex_ite_invar simp del: ifex_ite.simps)

definition "reads_inside_set f x \<equiv> (\<forall>assmt1 assmt2. (\<forall>p. p \<in> x \<longrightarrow> assmt1 p = assmt2 p) \<longrightarrow> f assmt1 = f assmt2)"

lemma reads_inside_set_subset: "reads_inside_set f a \<Longrightarrow> a \<subseteq> b \<Longrightarrow> reads_inside_set f b"
  unfolding reads_inside_set_def by blast

lemma reads_inside_set_restrict: "reads_inside_set f s \<Longrightarrow> reads_inside_set (bf_restrict i v f) (Set.remove i s)"
  unfolding reads_inside_set_def bf_restrict_def by force (* wow *)

lemma collect_upd_true: "Collect (x(y:= True)) = insert y (Collect x)" by auto
lemma collect_upd_false: "Collect (x(y:= False)) = Set.remove y (Collect x)" by auto metis

lemma reads_none: "reads_inside_set f {} \<Longrightarrow> f = bf_True \<or> f = bf_False"
  unfolding reads_inside_set_def by fast (* wow *)

lemma val_ifex_ite_subst: "\<lbrakk>ro_ifex i; ro_ifex t; ro_ifex e\<rbrakk> \<Longrightarrow> val_ifex (ifex_ite i t e) = bf_ite (val_ifex i) (val_ifex t) (val_ifex e)"
  using val_ifex_ite by blast

lemma 
  val_ifex_mk_ifex_equal:
  "reads_inside_set f (set vs) \<Longrightarrow> val_ifex (mk_ifex f vs) assmt = f assmt"
proof(induction vs arbitrary: f assmt)
  case Nil
  then show ?case using reads_none by auto
next
  case (Cons v vs)
  have "reads_inside_set (bf_restrict v x f) (set vs)" for x
    using reads_inside_set_restrict[OF Cons.prems] reads_inside_set_subset by fastforce
  from Cons.IH[OF this] show ?case 
    unfolding mk_ifex.simps val_ifex.simps bf_restrict_def
    by(subst val_ifex_ite_subst; simp add: bf_ite_def fun_upd_idem mk_ifex_ro)
qed

end