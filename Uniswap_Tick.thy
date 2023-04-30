theory Uniswap_Tick
  imports Uniswap_Common
begin


section \<open>Semantics\<close>

subsection \<open>Models of Tick\<close>

declare [[\<phi>trace_reasoning = 0]]

datatype tick_info = tick_info
  (growth: growth)
  (liquidityGross: real)
  (liquidityNet: real)
  (initialized: bool)

setup \<open>Sign.mandatory_path "tick_info"\<close>

definition \<open>map_growth F x = (case x of tick_info g l1 l2 i \<Rightarrow> tick_info (F g) l1 l2 i)\<close>
lemma [simp]: \<open>tick_info.map_growth F (tick_info g l1 l2 i) = (tick_info (F g) l1 l2 i)\<close>
  unfolding tick_info.map_growth_def by simp

definition \<open>map_initialized F x = (case x of tick_info g l1 l2 i \<Rightarrow> tick_info g l1 l2 (F i))\<close>
lemma [simp]: \<open>tick_info.map_initialized F (tick_info g l1 l2 i) = (tick_info g l1 l2 (F i))\<close>
  unfolding tick_info.map_initialized_def by simp

setup \<open>Sign.parent_path\<close>

definition \<open>map_liquidityGross F x = (case x of tick_info g l1 l2 i \<Rightarrow> tick_info g (F l1) l2 i)\<close>
lemma [simp]: \<open>map_liquidityGross F (tick_info g l1 l2 i) = (tick_info g (F l1) l2 i)\<close>
  unfolding map_liquidityGross_def by simp

definition \<open>map_liquidityNet F x = (case x of tick_info g l1 l2 i \<Rightarrow> tick_info g l1 (F l2) i)\<close>
lemma [simp]: \<open>map_liquidityNet F (tick_info g l1 l2 i) = (tick_info g l1 (F l2) i)\<close>
  unfolding map_liquidityNet_def by simp

hide_const (open) growth initialized

instantiation tick_info :: zero begin
definition zero_tick_info :: tick_info where [simp]: \<open>zero_tick_info = tick_info 0 0 0 False\<close>
instance ..
end

type_synonym ticks = \<open>tick \<Rightarrow> tick_info\<close>

(*
resource_space \<phi>uniswap =
  ticks :: \<open>UNIV::ticks nonsepable_mono_resource set\<close> (nonsepable_mono_resource)
  by (standard; simp add: set_eq_iff image_iff)


subsubsection \<open>Fiction\<close>

fiction_space \<phi>uniswap =
  ticks :: \<open>RES.ticks.basic_fiction \<F>_it\<close> (identity_fiction RES.ticks)
  by (standard; simp add: set_eq_iff image_iff) *)

section \<open>\<phi>-Types - Part I - Raw\<close>


subsection \<open>Tick Info Data\<close>

type_synonym opt_growths = \<open>tick \<Rightarrow> growth option\<close>

definition growth_outside :: \<open>growths \<Rightarrow> tick \<Rightarrow> growth \<Rightarrow> tick \<Rightarrow> growth\<close>
  where \<open>growth_outside abs_func tick delta current =
  (if tick \<le> current then (sum abs_func {MIN_TICK-1..<tick}) + delta
                      else (sum abs_func {tick..MAX_TICK}) - delta)\<close>

(*report: the spec of the tick_info.initialized is incorrect!
  it is not \<open>liquidity i \<noteq> 0\<close> 

  abst: real (physical) growth
  delta: is some if initialized.
*)
definition Invt_A_Tick :: \<open>tick \<Rightarrow> tick \<Rightarrow> liquiditys \<Rightarrow>  liquiditys
                                \<Rightarrow> growths \<Rightarrow> growth option \<Rightarrow> tick_info \<Rightarrow> bool \<close>
  where \<open>Invt_A_Tick i current liquidity_gross liquidity growth \<delta> ti
          \<longleftrightarrow> tick_info.liquidityGross ti = liquidity_gross i \<and>
              tick_info.liquidityNet ti = liquidity i - liquidity (i-1) \<and>
              pred_option (\<lambda>\<delta>. tick_info.growth ti = growth_outside growth i \<delta> current) \<delta> \<and>
              tick_info.initialized ti = (\<delta> \<noteq> None)
        \<close>

definition Invt_Ticks :: \<open>tick \<Rightarrow> liquiditys \<Rightarrow> liquiditys \<Rightarrow> growths \<Rightarrow> opt_growths
                               \<Rightarrow> ticks \<Rightarrow> bool\<close>
  where \<open>Invt_Ticks current liquidity_gross liquidity growth \<delta> ticks
          \<longleftrightarrow> (\<forall>i. Invt_A_Tick i current liquidity_gross liquidity growth (\<delta> i) (ticks i))
              \<and> current \<in> {MIN_TICK-1..MAX_TICK}
              \<and> (\<forall>k. liquidity_gross k = 0 \<longleftrightarrow> \<delta> k = None)
              \<and> (\<forall>k. liquidity_gross k = 0 \<longrightarrow> liquidity k = liquidity (k-1))
              \<and> (\<forall>k. 0 \<le> liquidity_gross k) \<and> (\<forall>k. 0 \<le> liquidity k) \<and> (\<forall>k. 0 \<le> growth k)
              \<and> (\<forall>k. liquidity_gross k \<noteq> 0 \<longrightarrow> k \<in> {MIN_TICK..MAX_TICK})\<close>

lemma Invt_Ticks_initialization:
  \<open>Invt_Ticks i Lg L gr \<delta> ticks \<Longrightarrow> \<delta> j = None \<longleftrightarrow> Lg j = 0\<close>
  unfolding Invt_Ticks_def Invt_A_Tick_def
  by auto


locale Tick_resource =
  fixes RawTicks :: \<open>(fiction, ticks) \<phi>\<close>
begin

definition Ticks :: \<open>(fiction, (liquiditys \<times> liquiditys \<times> growths \<times> tick \<times> opt_growths)) \<phi>\<close>
  where [\<phi>defs]: \<open>Ticks x = (case x of (Lg, liquidity, growth, current, \<delta>) \<Rightarrow>
                    ticks \<Ztypecolon> RawTicks \<s>\<u>\<b>\<j> ticks. Invt_Ticks current Lg liquidity growth \<delta> ticks)\<close>

(*A problem of the automatic transformation rule is,
  look, the source \<open>ticks\<close> and the target \<open>liquidity, growth, \<delta>\<close> has no common term,
  meaning if there are two \<open>ticks1 \<Ztypecolon> RawTicks\<heavy_comma> ticks2 \<Ztypecolon> RawTicks\<close>, it is impossible to determine
  which one is the desired one to be transformed, or any combination of them two.

  There is no problem if there is only one \<open>ticks \<Ztypecolon> RawTicks\<close>.
*)

lemma [\<phi>reason 1200]:
  \<open> \<p>\<r>\<e>\<m>\<i>\<s>\<e> Invt_Ticks current Lg liquidity growth \<delta> ticks
\<Longrightarrow> ticks \<Ztypecolon> RawTicks \<i>\<m>\<p>\<l>\<i>\<e>\<s> (Lg, liquidity, growth, current, \<delta>) \<Ztypecolon> Ticks\<close>
  \<medium_left_bracket> construct\<phi> \<open>(Lg, liquidity, growth, current, \<delta>) \<Ztypecolon> Ticks\<close> \<medium_right_bracket>. .

lemma [\<phi>reason 1200]:
  \<open> \<p>\<r>\<e>\<m>\<i>\<s>\<e> Invt_Ticks current Lg liquidity growth \<delta> ticks
\<Longrightarrow> ticks \<Ztypecolon> RawTicks \<i>\<m>\<p>\<l>\<i>\<e>\<s> (Lg, liquidity, growth, current, \<delta>) \<Ztypecolon> Ticks
    @action to Ticks\<close> \<medium_left_bracket> \<medium_right_bracket>. .

lemma [\<phi>reason 3000, \<phi>inhabitance_rule]:
  \<open> (Lg, liquidity, growth, current, \<delta>) \<Ztypecolon> Ticks
    \<i>\<m>\<p>\<l>\<i>\<e>\<s> ticks \<Ztypecolon> RawTicks \<s>\<u>\<b>\<j> ticks. Invt_Ticks current Lg liquidity growth \<delta> ticks
    @action to RawTicks\<close>
  \<medium_left_bracket> destruct\<phi> _ \<medium_right_bracket>. .

end

section \<open>Axiomatic Semantics of Abstract Operations\<close>

(*Someday when we finish the solidity semantics, we will instantiate this!*)
locale Tick_spec = Tick_resource +
fixes op_get_liquidityGross :: \<open>(VAL, VAL) proc'\<close>
and op_set_liquidityGross :: \<open>(VAL \<times> VAL, VAL) proc'\<close>
and op_get_liquidityNet :: \<open>(VAL, VAL) proc'\<close>
and op_set_liquidityNet :: \<open>(VAL \<times> VAL, VAL) proc'\<close>
and op_get_initialized :: \<open>(VAL, VAL) proc'\<close>
and op_set_initialized :: \<open>(VAL \<times> VAL, VAL) proc'\<close>
and op_get_feeGrowth0 :: \<open>(VAL, VAL) proc'\<close>
and op_set_feeGrowth0 :: \<open>(VAL \<times> VAL, VAL) proc'\<close>
and op_get_feeGrowth1 :: \<open>(VAL, VAL) proc'\<close>
and op_set_feeGrowth1 :: \<open>(VAL \<times> VAL, VAL) proc'\<close>
(*and op_get_tickCumulative :: \<open>(VAL, VAL) proc'\<close>
and op_set_tickCumulative :: \<open>(VAL \<times> VAL, VAL) proc'\<close>
and op_get_secondsPerLiquidity :: \<open>(VAL, VAL) proc'\<close>
and op_set_secondsPerLiquidity :: \<open>(VAL \<times> VAL, VAL) proc'\<close>
and op_get_seconds :: \<open>(VAL, VAL) proc'\<close>
and op_set_seconds :: \<open>(VAL \<times> VAL, VAL) proc'\<close> *)
assumes
    get_liquidityGross_\<phi>app[\<phi>synthesis 1200]:
      \<open> \<p>\<r>\<o>\<c> op_get_liquidityGross ri \<lbrace> f \<Ztypecolon> RawTicks\<heavy_comma> i \<Ztypecolon> \<v>\<a>\<l>[ri] Tick
                                   \<longmapsto> f \<Ztypecolon> RawTicks\<heavy_comma> (liquidityGross o f) i \<Ztypecolon> \<v>\<a>\<l> \<real> \<rbrace>\<close>
                                                    (* to prevent higher-order unification! *)
and set_liquidityGross_\<phi>app:
      \<open> \<p>\<r>\<o>\<c> op_set_liquidityGross (rv\<^bold>, ri)
            \<lbrace> f \<Ztypecolon> RawTicks\<heavy_comma> i \<Ztypecolon> \<v>\<a>\<l>[ri] Tick \<heavy_comma> v \<Ztypecolon> \<v>\<a>\<l>[rv] \<real>
                \<longmapsto> f(i := map_liquidityGross (\<lambda>_. v) (f i)) \<Ztypecolon> RawTicks\<heavy_comma> i \<Ztypecolon> \<v>\<a>\<l> Tick \<rbrace>\<close>
and get_liquidityNet_\<phi>app[\<phi>synthesis 1200]:
      \<open> \<p>\<r>\<o>\<c> op_get_liquidityNet ri
            \<lbrace> f \<Ztypecolon> RawTicks\<heavy_comma> i \<Ztypecolon> \<v>\<a>\<l>[ri] Tick
                \<longmapsto> f \<Ztypecolon> RawTicks\<heavy_comma> (liquidityNet o f) i \<Ztypecolon> \<v>\<a>\<l> \<real> \<rbrace>\<close>
and set_liquidityNet_\<phi>app:
      \<open> \<p>\<r>\<o>\<c> op_set_liquidityNet (rv\<^bold>, ri)
            \<lbrace> f \<Ztypecolon> RawTicks\<heavy_comma> i \<Ztypecolon> \<v>\<a>\<l>[ri] Tick \<heavy_comma> v \<Ztypecolon> \<v>\<a>\<l>[rv] \<real>
                \<longmapsto> f(i := map_liquidityNet (\<lambda>_. v) (f i)) \<Ztypecolon> RawTicks\<heavy_comma> i \<Ztypecolon> \<v>\<a>\<l> Tick \<rbrace>\<close>
and get_initialized_\<phi>app[\<phi>synthesis 1200]:
      \<open> \<p>\<r>\<o>\<c> op_get_initialized ri
            \<lbrace> f \<Ztypecolon> RawTicks\<heavy_comma> i \<Ztypecolon> \<v>\<a>\<l>[ri] Tick
                \<longmapsto> f \<Ztypecolon> RawTicks\<heavy_comma> (tick_info.initialized o f) i \<Ztypecolon> \<v>\<a>\<l> \<bool> \<rbrace>\<close>
and set_initialized_\<phi>app:
      \<open> \<p>\<r>\<o>\<c> op_set_initialized (rv\<^bold>, ri)
            \<lbrace> f \<Ztypecolon> RawTicks\<heavy_comma> i \<Ztypecolon> \<v>\<a>\<l>[ri] Tick \<heavy_comma> b \<Ztypecolon> \<v>\<a>\<l>[rv] \<bool>
                \<longmapsto> f(i := tick_info.map_initialized (\<lambda>_. b) (f i)) \<Ztypecolon> RawTicks\<heavy_comma> i \<Ztypecolon> \<v>\<a>\<l> Tick \<rbrace>\<close>
and get_feeGrowth0_\<phi>app[\<phi>synthesis 1200]:
      \<open> \<p>\<r>\<o>\<c> op_get_feeGrowth0 ri
            \<lbrace> f \<Ztypecolon> RawTicks\<heavy_comma> i \<Ztypecolon> \<v>\<a>\<l>[ri] Tick
                \<longmapsto> f \<Ztypecolon> RawTicks\<heavy_comma> (growth.fee0 o tick_info.growth o f) i \<Ztypecolon> \<v>\<a>\<l> \<real> \<rbrace>\<close>
and set_feeGrowth0_\<phi>app:
      \<open> \<p>\<r>\<o>\<c> op_set_feeGrowth0 (rv\<^bold>, ri)
            \<lbrace> f \<Ztypecolon> RawTicks\<heavy_comma> i \<Ztypecolon> \<v>\<a>\<l>[ri] Tick \<heavy_comma> r \<Ztypecolon> \<v>\<a>\<l>[rv] \<real>
                \<longmapsto> f(i := tick_info.map_growth (growth.map_fee0 (\<lambda>_. r)) (f i)) \<Ztypecolon> RawTicks\<heavy_comma> i \<Ztypecolon> \<v>\<a>\<l> Tick \<rbrace>\<close>
and get_feeGrowth1_\<phi>app[\<phi>synthesis 1200]:
      \<open> \<p>\<r>\<o>\<c> op_get_feeGrowth1 ri
            \<lbrace> f \<Ztypecolon> RawTicks\<heavy_comma> i \<Ztypecolon> \<v>\<a>\<l>[ri] Tick
                \<longmapsto> f \<Ztypecolon> RawTicks\<heavy_comma> (growth.fee1 o tick_info.growth o f) i \<Ztypecolon> \<v>\<a>\<l> \<real> \<rbrace>\<close>
and set_feeGrowth1_\<phi>app:
      \<open> \<p>\<r>\<o>\<c> op_set_feeGrowth1 (rv\<^bold>, ri)
            \<lbrace> f \<Ztypecolon> RawTicks\<heavy_comma> i \<Ztypecolon> \<v>\<a>\<l>[ri] Tick \<heavy_comma> r \<Ztypecolon> \<v>\<a>\<l>[rv] \<real>
                \<longmapsto> f(i := tick_info.map_growth (growth.map_fee1 (\<lambda>_. r)) (f i)) \<Ztypecolon> RawTicks\<heavy_comma> i \<Ztypecolon> \<v>\<a>\<l> Tick \<rbrace>\<close>
(* and get_tickCumulative_\<phi>app[\<phi>synthesis 1200]:
      \<open> \<p>\<r>\<o>\<c> op_get_tickCumulative ri
            \<lbrace> f \<Ztypecolon> RawTicks\<heavy_comma> i \<Ztypecolon> \<v>\<a>\<l>[ri] Tick
                \<longmapsto> f \<Ztypecolon> RawTicks\<heavy_comma> (growth.tickCumulative o tick_info.growth o f) i \<Ztypecolon> \<v>\<a>\<l> \<int> \<rbrace>\<close>
and set_tickCumulative_\<phi>app:
      \<open> \<p>\<r>\<o>\<c> op_set_tickCumulative (rv\<^bold>, ri)
            \<lbrace> f \<Ztypecolon> RawTicks\<heavy_comma> i \<Ztypecolon> \<v>\<a>\<l>[ri] Tick \<heavy_comma> v \<Ztypecolon> \<v>\<a>\<l>[rv] \<int>
                \<longmapsto> f(i := tick_info.map_growth (growth.map_tickCumulative (\<lambda>_. v)) (f i)) \<Ztypecolon> RawTicks\<heavy_comma> i \<Ztypecolon> \<v>\<a>\<l> Tick \<rbrace>\<close>
and get_secondsPerLiquidity_\<phi>app[\<phi>synthesis 1200]:
      \<open> \<p>\<r>\<o>\<c> op_get_secondsPerLiquidity ri
            \<lbrace> f \<Ztypecolon> RawTicks\<heavy_comma> i \<Ztypecolon> \<v>\<a>\<l>[ri] Tick
                \<longmapsto> f \<Ztypecolon> RawTicks\<heavy_comma> (growth.secondsPerLiquidity o tick_info.growth o f) i \<Ztypecolon> \<v>\<a>\<l> \<real> \<rbrace>\<close>
and set_secondsPerLiquidity_\<phi>app:
      \<open> \<p>\<r>\<o>\<c> op_set_secondsPerLiquidity (rv\<^bold>, ri)
            \<lbrace> f \<Ztypecolon> RawTicks\<heavy_comma> i \<Ztypecolon> \<v>\<a>\<l>[ri] Tick \<heavy_comma> r \<Ztypecolon> \<v>\<a>\<l>[rv] \<real>
                \<longmapsto> f(i := tick_info.map_growth (growth.map_secondsPerLiquidity (\<lambda>_. r)) (f i)) \<Ztypecolon> RawTicks\<heavy_comma> i \<Ztypecolon> \<v>\<a>\<l> Tick \<rbrace>\<close>
and get_seconds_\<phi>app[\<phi>synthesis 1200]:
      \<open> \<p>\<r>\<o>\<c> op_get_seconds ri
            \<lbrace> f \<Ztypecolon> RawTicks\<heavy_comma> i \<Ztypecolon> \<v>\<a>\<l>[ri] Tick
                \<longmapsto> f \<Ztypecolon> RawTicks\<heavy_comma> (growth.seconds o tick_info.growth o f) i \<Ztypecolon> \<v>\<a>\<l> \<int> \<rbrace>\<close>
and set_seconds_\<phi>app:
      \<open> \<p>\<r>\<o>\<c> op_set_seconds (rv\<^bold>, ri)
            \<lbrace> f \<Ztypecolon> RawTicks\<heavy_comma> i \<Ztypecolon> \<v>\<a>\<l>[ri] Tick \<heavy_comma> v \<Ztypecolon> \<v>\<a>\<l>[rv] \<int>
                \<longmapsto> f(i := tick_info.map_growth (growth.map_seconds (\<lambda>_. v)) (f i)) \<Ztypecolon> RawTicks\<heavy_comma> i \<Ztypecolon> \<v>\<a>\<l> Tick \<rbrace>\<close>
*)

section \<open>Verify\<close>

subsection \<open>Auxiliary Library\<close>

lemma interval_sub_1[simp]:
  \<open>A \<le> B \<Longrightarrow> {A..C} - {A..<B} = {B..C}\<close>
  for A :: int by auto

lemma sum_sub_1[simp]:
  \<open>A \<le> B \<and> B \<le> C \<Longrightarrow> sum f {A..C} - sum f {A..<B} = sum f {B..C}\<close>
  for f :: \<open>int \<Rightarrow> 'a::ab_group_add\<close>
  by (smt (verit, del_insts) atLeastLessThan_upto atLeastatMost_subset_iff finite_atLeastAtMost_int interval_sub_1 set_upto sum_diff)

lemma interval_sub_2[simp]:
  \<open>B \<le> C \<Longrightarrow> {A..C} - {B..C} = {A..<B}\<close> for A :: int by auto

lemma sum_sub_2[simp]:
  \<open>A \<le> B \<and> B \<le> C \<Longrightarrow> sum f {A..C} - sum f {B..C} = sum f {A..<B}\<close>
  for f :: \<open>int \<Rightarrow> 'a::ab_group_add\<close>
  using sum_diff interval_sub_2
  by (metis atLeastatMost_subset_iff dual_order.refl finite_atLeastAtMost_int)

abbreviation gSum \<comment> \<open>global sum\<close>
  where \<open>gSum growth \<equiv> (\<Sum>x = MIN_TICK-1..MAX_TICK. growth x)\<close>

abbreviation \<open>global_fee1_growth x \<equiv> growth.fee1 (gSum x)\<close>
abbreviation \<open>global_fee0_growth x \<equiv> growth.fee0 (gSum x)\<close>

lemma gSum_subtract1[simp]:
  \<open> MIN_TICK-1 \<le> i \<and> i \<le> j \<and> j \<le> MAX_TICK
\<Longrightarrow> gSum growth - growth_outside growth i \<delta> j = growth_outside growth i \<delta> (i-1)\<close>
  unfolding growth_outside_def by auto

lemma gSum_subtract2[simp]:
  \<open> MIN_TICK-1 \<le> j \<and> j < i \<and> i \<le> MAX_TICK
\<Longrightarrow> gSum growth - growth_outside growth i \<delta> j = growth_outside growth i \<delta> i\<close>
  unfolding growth_outside_def by auto

lemma growth_outside_shift_mono:
  \<open> i \<le> j \<and> j \<le> k   \<or>   j < i \<and> k \<le> j
\<Longrightarrow> growth_outside growth i \<delta> j = growth_outside growth i \<delta> k\<close>
  unfolding growth_outside_def by auto

lemma sum_plus_fun[simp]:
  \<open>finite S \<Longrightarrow> sum (f + g) S = sum f S + sum g S\<close>
  unfolding plus_fun_def
  using sum.distrib by blast


abbreviation \<open>next_initialized Lg i j \<equiv> (\<forall>k. i < k \<and> k < j \<longrightarrow> Lg k = 0)\<close>

lemma (in Tick_resource) shift_current_tick_\<phi>app:
  \<open> \<p>\<r>\<e>\<m>\<i>\<s>\<e> j \<in> {MIN_TICK-1..MAX_TICK}
\<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> (if j \<le> i then next_initialized Lg j (i+1) else next_initialized Lg i (j+1))
\<Longrightarrow> (Lg, L, g, i, \<delta>) \<Ztypecolon> Ticks \<i>\<m>\<p>\<l>\<i>\<e>\<s> (Lg, L, g, j, \<delta>) \<Ztypecolon> Ticks \<close>
  \<medium_left_bracket> to \<open>RawTicks\<close> \<medium_right_bracket>
    using \<phi> by (auto simp add: Invt_Ticks_def Invt_A_Tick_def,
                smt (verit) Invt_A_Tick_def Invt_Ticks_def growth_outside_def option.pred_inject(1) option.pred_inject(2) the_\<phi>lemmata) .

lemma (in Tick_resource) shift_current_tick_\<Delta>_\<phi>app:
  \<open> \<p>\<r>\<e>\<m>\<i>\<s>\<e> j \<in> {MIN_TICK-1..MAX_TICK}
\<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> (if j \<le> i then next_initialized Lg j (i+1) else next_initialized Lg i (j+1))
\<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> (if j \<le> i then (\<forall>k. k < j \<or> k > i \<longrightarrow> \<Delta> k = 0) else (\<forall>k. k < i \<or> k > j \<longrightarrow> \<Delta> k = 0))
\<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> (\<forall>k. 0 \<le> \<Delta> k)
\<Longrightarrow> (Lg, L, g, i, \<delta>) \<Ztypecolon> Ticks \<i>\<m>\<p>\<l>\<i>\<e>\<s> (Lg, L, g + \<Delta>, j, \<delta>) \<Ztypecolon> Ticks \<close>
  \<medium_left_bracket> to \<open>RawTicks\<close> \<medium_right_bracket>
    using \<phi> apply (auto simp add: Invt_Ticks_def Invt_A_Tick_def plus_fun)
    subgoal for i' apply (cases \<open>\<delta> i'\<close>; clarsimp simp add: growth_outside_def)
      apply (cases \<open>j \<le> i\<close>; simp) 
      apply (cases \<open>i' \<le> j\<close>; simp)
      apply (smt (verit, best) option.pred_inject(2))
      apply (cases \<open>i' \<le> i\<close>; simp)
       apply (smt (verit, best) option.pred_inject(2))
      apply (cases \<open>i' \<le> i\<close>, simp)
      apply (smt (verit, best) option.pred_inject(2))
      by (smt (verit) option.distinct(1) option.pred_inject(2))
    by (meson add_order_0_class.add_nonneg_nonneg)
      .

(* lemma (in Tick_resource) shift_current_tick_\<phi>app:
  \<open> \<p>\<r>\<e>\<m>\<i>\<s>\<e> j \<in> {MIN_TICK-1..MAX_TICK}
\<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> (if j \<le> i then next_initialized Lg j (i+1) else next_initialized Lg i (j+1))
\<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> (if i \<le> j then (\<forall>k. k < i \<or> k > j \<longrightarrow> \<Delta> k = 0) else (\<forall>k. k < j \<or> k \<ge> i \<longrightarrow> \<Delta> k = 0)
\<Longrightarrow> (Lg, L, g, i, \<delta>) \<Ztypecolon> Ticks \<i>\<m>\<p>\<l>\<i>\<e>\<s> (Lg, L, g, j, \<delta>) \<Ztypecolon> Ticks \<close>
  \<medium_left_bracket> to \<open>RawTicks\<close> \<medium_right_bracket>
*)


lemma sum_update:
  \<open> finite S
\<Longrightarrow> j \<in> S
\<Longrightarrow> sum (\<lambda>k. if k = j then f j + \<delta> else f k) S = sum f S + \<delta>\<close>
  by (simp add: add.assoc add.commute sum.remove)

lemma gSum_update[simp]:
  \<open> j \<in> {MIN_TICK - 1 .. MAX_TICK}
\<Longrightarrow> gSum (\<lambda>k. if k = j then f j + \<delta> else f k) = gSum f + \<delta>\<close>
  using sum_update[where S=\<open>{MIN_TICK-1..MAX_TICK}\<close>, simplified] by auto




context Tick_spec begin

proc getFeeGrowthInside:
  premises \<open>0 < Lg lower\<close> and \<open>0 < Lg upper\<close> (*They mean the upper tick and the lower tick is initialized*)
    and    \<open>lower < upper\<close>
  premises \<open>global_fee0 = growth.fee0 (gSum growth)\<close> (*global_fee0 is the sum of all the growth at every ticks*)
    and    \<open>global_fee1 = growth.fee1 (gSum growth)\<close>
  input \<open>(Lg, liq, growth, current, \<delta>) \<Ztypecolon> Ticks \<heavy_comma>
          lower \<Ztypecolon> \<v>\<a>\<l> Tick \<heavy_comma> upper \<Ztypecolon> \<v>\<a>\<l> Tick \<heavy_comma> current \<Ztypecolon> \<v>\<a>\<l> Tick \<heavy_comma> global_fee0 \<Ztypecolon> \<v>\<a>\<l> \<real> \<heavy_comma> global_fee1 \<Ztypecolon> \<v>\<a>\<l> \<real>\<close>
  output \<open>(Lg, liq, growth, current, \<delta>) \<Ztypecolon> Ticks \<heavy_comma>
          growth.fee0 (sum growth {lower..<upper} - the (\<delta> lower) + the (\<delta> upper)) \<Ztypecolon> \<v>\<a>\<l> \<real> \<heavy_comma>
          growth.fee1 (sum growth {lower..<upper} - the (\<delta> lower) + the (\<delta> upper)) \<Ztypecolon> \<v>\<a>\<l> \<real>\<close>
  is [routine_basic]
  \<medium_left_bracket> to \<open>RawTicks\<close> ;;

    obtain \<delta>_lower \<delta>_upper where \<delta>_lower[simp]: \<open>\<delta> lower = Some \<delta>_lower\<close>
                            and \<delta>_upper[simp]: \<open>\<delta> upper = Some \<delta>_upper\<close>
      by (metis Invt_Ticks_initialization not_None_eq not_less_iff_gr_or_eq the_\<phi>(12) the_\<phi>(13) the_\<phi>lemmata(7))

    note lower_simps[simp] =
          \<open>Invt_Ticks current Lg liq growth \<delta> ticks\<close>[unfolded Invt_Ticks_def Invt_A_Tick_def
                  growth_outside_def, THEN conjunct1, THEN spec[where x=lower], simplified]
    note upper_simps[simp] =
          \<open>Invt_Ticks current Lg liq growth \<delta> ticks\<close>[unfolded Invt_Ticks_def Invt_A_Tick_def
                  growth_outside_def, THEN conjunct1, THEN spec[where x=upper], simplified] ;;

    if \<open>$lower \<le> $current\<close> \<medium_left_bracket>
      $lower get_feeGrowth0
      $lower get_feeGrowth1
    \<medium_right_bracket>. \<medium_left_bracket>
      $global_fee0 sub ($lower get_feeGrowth0)
      $global_fee1 sub ($lower get_feeGrowth1)
    \<medium_right_bracket>. \<rightarrow> val fee0_below, fee1_below

    if \<open>$current < $upper\<close> \<medium_left_bracket>
      have [simp]: \<open>\<not> (upper \<le> current)\<close> using \<open>current < upper\<close> by linarith ;;
      $upper get_feeGrowth0
      $upper get_feeGrowth1
    \<medium_right_bracket>. \<medium_left_bracket>
      have [simp]: \<open>(upper \<le> current)\<close> using \<open>\<not> (current < upper)\<close> by linarith ;;
      $global_fee0 sub ($upper get_feeGrowth0)
      $global_fee1 sub ($upper get_feeGrowth1)
    \<medium_right_bracket>. \<rightarrow> val fee0_above, fee1_above

    note add_diff_eq[simp] fee0_sum[simp] fee1_sum[simp] diff_diff_eq[symmetric, simp] ;;
      
    \<open>$global_fee0 - $fee0_below - $fee0_above\<close>
    \<open>$global_fee1 - $fee1_below - $fee1_above\<close>
  \<medium_right_bracket>. .

thm getFeeGrowthInside_def[simplified \<phi>V_simps]
thm getFeeGrowthInside_\<phi>app

(*\<heavy_comma>
          liq i - liq current \<Ztypecolon> \<v>\<a>\<l> \<int> *)

declare Invt_Ticks_def[simp] Invt_A_Tick_def[simp]

proc tick_cross:
  premises \<open>0 < Lg i\<close>
    and    \<open>if i \<le> j then next_initialized Lg i (j+1) else next_initialized Lg j i\<close>
    and    \<open>if i \<le> j then (\<forall>k. k < i \<or> k > j \<longrightarrow> \<Delta> k = 0) else (\<forall>k. k < j \<or> k \<ge> i \<longrightarrow> \<Delta> k = 0)\<close>
    and    \<open>(\<forall>k. 0 \<le> \<Delta> k)\<close>
  premises \<open>(fee0, fee1) = gSum growth + gSum \<Delta>\<close> (*global_fee0 is the sum of all the growth at every ticks*)
(*    and    \<open>sec_per_liq = growth.secondsPerLiquidity (gSum growth)\<close>
    and    \<open>tick_cumu = growth.tickCumulative (gSum growth)\<close>
    and    \<open>time = growth.seconds (gSum growth)\<close>*)
  input  \<open>(Lg, liq, growth, j, \<delta>) \<Ztypecolon> Ticks \<heavy_comma> i \<Ztypecolon> \<v>\<a>\<l> Tick \<heavy_comma> fee0 \<Ztypecolon> \<v>\<a>\<l> \<real> \<heavy_comma> fee1 \<Ztypecolon> \<v>\<a>\<l> \<real>\<close>
        (* sec_per_liq \<Ztypecolon> \<v>\<a>\<l> \<real>\<heavy_comma> tick_cumu \<Ztypecolon> \<v>\<a>\<l> \<int> \<heavy_comma> time \<Ztypecolon> \<v>\<a>\<l> \<int> *)
  output \<open>(Lg, liq, growth + \<Delta>, (if i \<le> j then i - 1 else i), \<delta>) \<Ztypecolon> Ticks\<heavy_comma> liq i - liq (i - 1) \<Ztypecolon> \<v>\<a>\<l> \<real>\<close>
  is [routine]
  \<medium_left_bracket> to \<open>RawTicks\<close> \<exists>ticks

  obtain fee0' fee1' (*spl' tc' time'*) liqG' liqN' init'
    where Tick_i[simp]: \<open>ticks i = tick_info (fee0', fee1') liqG' liqN' init'\<close> (*(fee0', fee1', spl', tc', time')*)
    by (metis surj_pair tick_info.exhaust)

  ;; $i set_feeGrowth0 ($fee0 sub ($i get_feeGrowth0))
        set_feeGrowth1 ($fee1 sub ($i get_feeGrowth1)) 
     (* set_secondsPerLiquidity ($sec_per_liq sub ($i get_secondsPerLiquidity))
        set_tickCumulative ($tick_cumu sub ($i get_tickCumulative))
        set_seconds ($time sub ($i get_seconds))*) ;;
  pure_fact x1: \<open>i \<le> j \<Longrightarrow> \<forall>k \<in> {MIN_TICK-1..<i}. \<Delta> k = 0\<close>
        and \<open>i \<le> j \<Longrightarrow> sum \<Delta> {MIN_TICK-1..<i} = 0\<close>
        and x2: \<open>i \<le> j \<Longrightarrow> sum \<Delta> {i..MAX_TICK} = gSum \<Delta>\<close>
        and x3: \<open>i \<le> j \<Longrightarrow> i' \<le> i \<Longrightarrow> sum \<Delta> {MIN_TICK - 1..<i'} = 0\<close> for i'
        and \<open>i \<le> j \<Longrightarrow> \<forall>k \<in> {j<..MAX_TICK}. \<Delta> k = 0\<close>
        and x4: \<open>i \<le> j \<Longrightarrow> j < i' \<Longrightarrow> sum \<Delta> {i'..MAX_TICK} = 0\<close> for i'
        and \<open>\<not> i \<le> j \<Longrightarrow> \<forall>k \<in> {i..MAX_TICK}. \<Delta> k = 0\<close>
        and \<open>\<not> i \<le> j \<Longrightarrow> sum \<Delta> {i..MAX_TICK} = 0\<close>
        and y3: \<open>\<not> i \<le> j \<Longrightarrow> sum \<Delta> {MIN_TICK-1..<i} = gSum \<Delta>\<close>
        and y4: \<open>\<not> i \<le> j \<Longrightarrow> i' \<le> j \<Longrightarrow> sum \<Delta> {MIN_TICK - 1..<i'} = 0\<close> for i'
        and y5: \<open>\<not> i \<le> j \<Longrightarrow> i < i' \<Longrightarrow> sum \<Delta> {i'..MAX_TICK} = 0\<close> for i'
        and a1: \<open>\<delta> i = Some (a, b) \<Longrightarrow> tick_info.initialized (ticks i)\<close> for a b i
        and a2: \<open>\<delta> i = Some (a, b) \<Longrightarrow> tick_info.growth (ticks i) = growth_outside growth i (a,b) j\<close> for i a b
        and t1: \<open>(fee0 - fee0', fee1 - fee1') = (fee0, fee1) - (fee0', fee1')\<close>
(*
  have th1[simp]:
        \<open>\<And>A. (growth.fee0 A - fee0', growth.fee1 A - fee1') = A - (fee0', fee1')\<close>
        (* (growth.fee0 A - fee0', growth.fee1 A - fee1', growth.tickCumulative A - spl',
              growth.secondsPerLiquidity A - tc', growth.seconds A - time')
          = A - (fee0', fee1', spl', tc', time') *)
    by (case_tac A; simp)
  note th2 = \<open>Invt_Ticks j Lg liq growth \<delta> ticks\<close>[unfolded Invt_Ticks_def Invt_A_Tick_def]
  note th3 = th2[THEN conjunct1] ;; *)
  ;;
  $i get_liquidityNet
  \<medium_right_bracket> unfolding Invt_Ticks_def Invt_A_Tick_def
    apply (auto simp add: \<phi> plus_fun)
    apply (metis Tick_i the_\<phi>(10) tick_info.sel(2))
    apply (metis Tick_i the_\<phi>(10) tick_info.sel(3))
    apply (insert a2[of i], cases \<open>\<delta> i\<close>; clarsimp simp add: growth_outside_def x2)
    using t1 the_\<phi>(13) the_\<phi>lemmata(1) the_\<phi>lemmata(2) apply fastforce
    using the_\<phi>lemmata(3) apply fastforce
    using a1 apply fastforce
    subgoal for i' apply (insert a2[of i'], cases \<open>i' < i\<close>)
      apply (cases \<open>\<delta> i'\<close>; clarsimp simp add: growth_outside_def x2 x3)
      apply (cases \<open>i' \<le> j\<close>)
      using that(2) the_\<phi>lemmata(6) apply force
      by (cases \<open>\<delta> i'\<close>; clarsimp simp add: growth_outside_def x4)
    using the_\<phi>lemmata(1) apply fastforce
    using the_\<phi>lemmata(2) apply force
    apply (simp add: add_order_0_class.add_nonneg_nonneg the_\<phi>(14) the_\<phi>lemmata(10))
    apply (metis Tick_i the_\<phi>(10) tick_info.sel(3))
    apply (metis Tick_i the_\<phi>(10) tick_info.sel(2))
    apply (metis Tick_i the_\<phi>(10) tick_info.sel(3))
    apply (insert a2[of i], cases \<open>\<delta> i\<close>; clarsimp simp add: growth_outside_def x2 y3)
    using t1 the_\<phi>(13) the_\<phi>lemmata(1) the_\<phi>lemmata(2) apply fastforce
    using the_\<phi>lemmata(3) apply fastforce
    using a1 apply fastforce
    subgoal for i' apply (insert a2[of i'], cases \<open>i' \<le> j\<close>)
       apply (cases \<open>\<delta> i'\<close>; clarsimp simp add: growth_outside_def y4)
      apply (cases \<open>i' \<le> i\<close>)
      using the_\<phi>(16) the_\<phi>lemmata(6) apply force
      by (cases \<open>\<delta> i'\<close>; clarsimp simp add: growth_outside_def y5)
    using the_\<phi>lemmata(1) apply force
    apply (simp add: add_order_0_class.add_nonneg_nonneg the_\<phi>(14) the_\<phi>lemmata(10))
    by (metis Tick_i the_\<phi>(10) tick_info.sel(3))
  .

end

end