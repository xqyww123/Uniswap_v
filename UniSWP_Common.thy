theory UniSWP_Common
  imports HOL.Real Phi_Semantics.PhiSem_CF_Solidity
          Phi_Semantics.PhiSem_Real_Abst_Int
          Phi_Semantics.PhiSem_CF_Routine
          Phi_Semantics.PhiSem_Variable
begin


type_synonym token = int
type_synonym fee = real
type_synonym address = int
type_synonym tick = int
type_synonym growth = \<open>fee \<comment> \<open>fee0\<close> \<times> fee \<comment> \<open>fee1\<close>\<close> (* \<times> int \<times> real \<times> int, we don't consider observation feature now *)
type_synonym liquidity = \<open>tick \<Rightarrow> real\<close>
type_synonym growths = \<open>tick \<Rightarrow> growth\<close>


setup \<open>Sign.mandatory_path "growth"\<close>

definition fee0 :: \<open>growth \<Rightarrow> real\<close> where \<open>fee0 = fst\<close>
definition map_fee0 :: "(real \<Rightarrow> real) \<Rightarrow> growth \<Rightarrow> growth" where \<open>map_fee0 = apfst\<close>
lemma fee0[simp]: \<open>growth.fee0 (a,b) = a\<close> unfolding growth.fee0_def by simp
lemma map_fee0[simp]: \<open>growth.map_fee0 f (a,b) = (f a,b)\<close> unfolding growth.map_fee0_def by simp
lemma fee0_0[simp]: \<open>growth.fee0 0 = 0\<close> unfolding zero_prod_def by simp

interpretation fee0: homo_add \<open>growth.fee0\<close> by (standard; case_tac x; case_tac y; simp)
interpretation fee0_funcomp: homo_add \<open>(o) growth.fee0\<close> ..
interpretation fee0: homo_zero \<open>growth.fee0\<close> by (standard; simp add: zero_prod_def)
interpretation fee0_funcomp: homo_zero \<open>(o) growth.fee0\<close> ..


definition fee1 :: \<open>growth \<Rightarrow> real\<close> where \<open>fee1 = snd\<close>
definition map_fee1 :: "(real \<Rightarrow> real) \<Rightarrow> growth \<Rightarrow> growth" where \<open>map_fee1 = apsnd\<close>
lemma fee1[simp]: \<open>growth.fee1 (a,b) = b\<close> unfolding growth.fee1_def by simp
lemma map_fee1[simp]: \<open>growth.map_fee1 f (a,b) = (a,f b)\<close> unfolding growth.map_fee1_def by simp
lemma fee1_0[simp]: \<open>growth.fee1 0 = 0\<close> unfolding zero_prod_def by simp

interpretation fee1: homo_add \<open>growth.fee1\<close> by (standard; case_tac x; case_tac y; simp)
interpretation fee1_funcomp: homo_add \<open>(o) growth.fee1\<close> ..
interpretation fee1: homo_zero \<open>growth.fee1\<close> by (standard; simp add: zero_prod_def)
interpretation fee1_funcomp: homo_zero \<open>(o) growth.fee1\<close> ..



(*
definition \<open>tickCumulative (x::growth) = (case x of (a,b,c,d,e) \<Rightarrow> c)\<close>
definition \<open>map_tickCumulative f (x::growth) = (case x of (a,b,c,d,e) \<Rightarrow> ((a,b,f c,d,e) :: growth))\<close>
lemma [simp]: \<open>growth.tickCumulative (a,b,c,d,e) = c\<close> unfolding growth.tickCumulative_def by simp
lemma [simp]: \<open>growth.map_tickCumulative f (a,b,c,d,e) = (a,b,f c,d,e)\<close> unfolding growth.map_tickCumulative_def by simp

definition \<open>secondsPerLiquidity (x::growth) = (case x of (a,b,c,d,e) \<Rightarrow> d)\<close>
definition \<open>map_secondsPerLiquidity f (x::growth) = (case x of (a,b,c,d,e) \<Rightarrow> ((a,b,c,f d,e) :: growth))\<close>
lemma [simp]: \<open>growth.secondsPerLiquidity (a,b,c,d,e) = d\<close> unfolding growth.secondsPerLiquidity_def by simp
lemma [simp]: \<open>growth.map_secondsPerLiquidity f (a,b,c,d,e) = (a,b,c,f d,e)\<close> unfolding growth.map_secondsPerLiquidity_def by simp

definition \<open>seconds (x::growth) = (case x of (a,b,c,d,e) \<Rightarrow> e)\<close>
definition \<open>map_seconds f (x::growth) = (case x of (a,b,c,d,e) \<Rightarrow> ((a,b,c,d,f e) :: growth))\<close>
lemma [simp]: \<open>growth.seconds (a,b,c,d,e) = e\<close> unfolding growth.seconds_def by simp
lemma [simp]: \<open>growth.map_seconds f (a,b,c,d,e) = (a,b,c,d,f e)\<close> unfolding growth.map_seconds_def by simp
*)
setup \<open>Sign.parent_path\<close>

lemma fee0_plus_homo[simp]:
  \<open>growth.fee0 (a + b) = growth.fee0 a + growth.fee0 b\<close>
  by (cases a; cases b; simp)

lemma fee0_sub_homo[simp]:
  \<open>growth.fee0 (a - b) = growth.fee0 a - growth.fee0 b\<close>
  by (cases a; cases b; simp)

lemma fee0_sum:
  \<open>growth.fee0 (sum f S) = sum (growth.fee0 o f) S\<close>
  by (metis add.right_neutral add_diff_cancel_left' fee0_plus_homo sum_comp_morphism)

lemma fee1_plus_homo[simp]:
  \<open>growth.fee1 (a + b) = growth.fee1 a + growth.fee1 b\<close>
  by (cases a; cases b; simp)

lemma fee1_sub_homo[simp]:
  \<open>growth.fee1 (a - b) = growth.fee1 a - growth.fee1 b\<close>
  by (cases a; cases b; simp)

lemma fee1_sum:
  \<open>growth.fee1 (sum f S) = sum (growth.fee1 o f) S\<close>
  by (metis add.right_neutral add_diff_cancel_left' fee1_plus_homo sum_comp_morphism)





datatype apos_info \<comment> \<open>abstract pos info\<close> = apos_info
  (liquidity: token)
  (revenue0: fee) \<comment> \<open>All time revenue, no matter whether is updated\<close>
  (revenue1: fee)
  (withdrawn0: fee) \<comment> \<open>the amount that the user has withdrawn\<close>
  (withdrawn1: fee)

hide_const (open) liquidity revenue0 revenue1 withdrawn0 withdrawn1

text \<open>The implementation records a settled revenue and the timestamp of the last settling.
  It will not calculate the actual revenue in time until an explicit update operation is invoked.
  Here, we specify the system using the in-time actual revenue, intuitively reflecting the system behavior.
\<close>



(*a quick formalization of Solidity address, which should be given
 in the semantic formalization of Solidity.*)
definition Address :: \<open>(VAL, address) \<phi>\<close>
  where [\<phi>defs]: \<open>Address a = (a \<Ztypecolon> \<int>)\<close>

lemma [\<phi>reason 1200]:
  \<open> \<t>\<h>\<r>\<e>\<s>\<h>\<o>\<l>\<d> 1
\<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> i = j
\<Longrightarrow> i \<Ztypecolon> \<int> \<i>\<m>\<p>\<l>\<i>\<e>\<s> j \<Ztypecolon> Address\<close>
  \<medium_left_bracket> construct\<phi> \<open>i \<Ztypecolon> Address\<close> \<medium_right_bracket>. .

lemma [\<phi>reason 1200]:
  \<open> i \<Ztypecolon> \<int> \<i>\<m>\<p>\<l>\<i>\<e>\<s> i \<Ztypecolon> Address @action to Address\<close> \<medium_left_bracket> \<medium_right_bracket>. .

lemma [\<phi>reason 1200]:
  \<open> \<t>\<h>\<r>\<e>\<s>\<h>\<o>\<l>\<d> 1
\<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> i = j
\<Longrightarrow> i \<Ztypecolon> Address \<i>\<m>\<p>\<l>\<i>\<e>\<s> j \<Ztypecolon> \<int> \<close>
  \<medium_left_bracket> destruct\<phi> _ \<medium_right_bracket>. .

lemma [\<phi>reason 1200, \<phi>inhabitance_rule]: \<open>i \<Ztypecolon> Address \<i>\<m>\<p>\<l>\<i>\<e>\<s> i \<Ztypecolon> \<int> @action to \<int>\<close> \<medium_left_bracket> \<medium_right_bracket>. .

lemma [\<phi>reason 1000]: "\<phi>Equal Address (\<lambda>x y. True) (=)" \<medium_left_bracket> to \<int> \<medium_right_bracket>. .

lemma [\<phi>reason 1000]: \<open>\<phi>SemType (x \<Ztypecolon> Address) aint\<close> \<medium_left_bracket> to \<int> \<medium_right_bracket>. .

lemma [\<phi>reason 1000]: "\<phi>Zero aint Address 0" \<medium_left_bracket> \<open>0 \<Ztypecolon> \<int>\<close> \<medium_right_bracket>. .



subsection \<open>Tick\<close>

definition \<open>MIN_TICK = (-887272::int)\<close>
definition \<open>MAX_TICK = ( 887272::int)\<close>

lemma MIN_TICK_LT_MAX_TICK[simp]:
  \<open>MIN_TICK < MAX_TICK\<close>
  unfolding MIN_TICK_def MAX_TICK_def by simp

lemma MM_TICK_LT_0[simp]:
  \<open>MIN_TICK < 0\<close> \<open>0 < MAX_TICK\<close>
  unfolding MIN_TICK_def MAX_TICK_def by simp_all

lemma MM_TICK_LE_0[simp]:
  \<open>MIN_TICK \<le> 0\<close> \<open>0 \<le> MAX_TICK\<close>
  unfolding MIN_TICK_def MAX_TICK_def by simp_all

lemma [\<phi>reason 1000]: \<open>Is_Literal MIN_TICK\<close> unfolding Is_Literal_def ..
lemma [\<phi>reason 1000]: \<open>Is_Literal MAX_TICK\<close> unfolding Is_Literal_def ..

proc (nodef) MIN_TICK[\<phi>synthesis 1100]:
  input \<open>Void\<close>
  output \<open>MIN_TICK \<Ztypecolon> \<v>\<a>\<l> \<int>\<close>
  \<medium_left_bracket> op_const_aint[where x=MIN_TICK] \<medium_right_bracket>. .

proc (nodef) MAX_TICK[\<phi>synthesis 1100]:
  input \<open>Void\<close>
  output \<open>MAX_TICK \<Ztypecolon> \<v>\<a>\<l> \<int>\<close>
  \<medium_left_bracket> op_const_aint[where x=MAX_TICK] \<medium_right_bracket>. .



definition Tick :: \<open>(VAL, tick) \<phi>\<close> where [\<phi>defs]: \<open>Tick i = (i \<Ztypecolon> \<int> \<s>\<u>\<b>\<j> i \<in> {MIN_TICK..MAX_TICK})\<close>

lemma [\<phi>reason 1200]:
  \<open> \<t>\<h>\<r>\<e>\<s>\<h>\<o>\<l>\<d> 1
\<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> i = j
\<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> j \<in> {MIN_TICK..MAX_TICK}
\<Longrightarrow> i \<Ztypecolon> \<int> \<i>\<m>\<p>\<l>\<i>\<e>\<s> j \<Ztypecolon> Tick\<close>
  \<medium_left_bracket> construct\<phi> \<open>i \<Ztypecolon> Tick\<close> \<medium_right_bracket>. .

lemma [\<phi>reason 1200]:
  \<open> \<p>\<r>\<e>\<m>\<i>\<s>\<e> i \<in> {MIN_TICK..MAX_TICK}
\<Longrightarrow> i \<Ztypecolon> \<int> \<i>\<m>\<p>\<l>\<i>\<e>\<s> i \<Ztypecolon> Tick @action to Tick\<close> \<medium_left_bracket> \<medium_right_bracket>. .

lemma [\<phi>reason 1200]:
  \<open> \<t>\<h>\<r>\<e>\<s>\<h>\<o>\<l>\<d> 1
\<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> i = j
\<Longrightarrow> i \<Ztypecolon> Tick \<i>\<m>\<p>\<l>\<i>\<e>\<s> j \<Ztypecolon> \<int> \<a>\<n>\<d> i \<in> {MIN_TICK..MAX_TICK}\<close>
  \<medium_left_bracket> destruct\<phi> _ \<medium_right_bracket>. .

lemma [\<phi>reason 1200, \<phi>inhabitance_rule]:
  \<open>i \<Ztypecolon> Tick \<i>\<m>\<p>\<l>\<i>\<e>\<s> i \<Ztypecolon> \<int> \<a>\<n>\<d> i \<in> {MIN_TICK..MAX_TICK} @action to \<int>\<close> \<medium_left_bracket> \<medium_right_bracket>. .

lemma [\<phi>reason 1000]: "\<phi>Equal Tick (\<lambda>x y. True) (=)" \<medium_left_bracket> to \<int> \<medium_right_bracket>. .

lemma [\<phi>reason 1000]: \<open>\<phi>SemType (x \<Ztypecolon> Tick) aint\<close> \<medium_left_bracket> to \<int> \<medium_right_bracket>. .

lemma [\<phi>reason 1000]: "\<phi>Zero aint Tick 0" \<medium_left_bracket> \<open>0 \<Ztypecolon> \<int>\<close> \<medium_right_bracket>. .



end