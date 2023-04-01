theory UniSWP_Tick
  imports UniSWP_Common
begin


section \<open>Semantics\<close>

subsection \<open>Models of Tick\<close>

(*We do this ugly job because prod is configured with all algebraic properties!, like ring*)
declare [[\<phi>trace_reasoning = 0]]

datatype tick_info = tick_info
  (growth: growth)
  (liquidityGross: int)
  (liquidityNet: int)
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
definition Invt_A_Tick :: \<open>tick \<Rightarrow> tick \<Rightarrow> liquidity
                                \<Rightarrow> growths \<Rightarrow> growth option \<Rightarrow> tick_info \<Rightarrow> bool \<close>
  where \<open>Invt_A_Tick i current liquidity growth \<delta> ti
          \<longleftrightarrow> tick_info.liquidityGross ti = liquidity i \<and>
              tick_info.liquidityNet ti = liquidity (i + 1) - liquidity i \<and>
              pred_option (\<lambda>\<delta>. tick_info.growth ti = growth_outside growth i \<delta> current) \<delta> \<and>
              tick_info.initialized ti = (\<delta> \<noteq> None)
        \<close>

definition Invt_Ticks :: \<open>tick \<Rightarrow> liquidity \<Rightarrow> growths \<Rightarrow> opt_growths
                               \<Rightarrow> ticks \<Rightarrow> bool\<close>
  where \<open>Invt_Ticks current liquidity abst \<delta> ticks
          \<longleftrightarrow> (\<forall>i. Invt_A_Tick i current liquidity abst (\<delta> i) (ticks i))
              \<and> current \<in> {MIN_TICK-1..MAX_TICK}\<close>

locale Tick_resource =
  fixes RawTicks :: \<open>(fiction, ticks) \<phi>\<close>
begin

definition Ticks :: \<open>tick \<Rightarrow> opt_growths \<Rightarrow> (fiction, (liquidity \<times> growths)) \<phi>\<close>
  where [\<phi>defs]: \<open>Ticks current \<delta> = (\<lambda>(liquidity, growth).
                    ticks \<Ztypecolon> RawTicks \<s>\<u>\<b>\<j> ticks. Invt_Ticks current liquidity growth \<delta> ticks)\<close>

(*A problem of the automatic transformation rule is,
  look, the source \<open>ticks\<close> and the target \<open>liquidity, growth, \<delta>\<close> has no common term,
  meaning if there are two \<open>ticks1 \<Ztypecolon> RawTicks\<heavy_comma> ticks2 \<Ztypecolon> RawTicks\<close>, it is impossible to determine
  which one is the desired one to be transformed, or any combination of them two.

  There is no problem if there is only one \<open>ticks \<Ztypecolon> RawTicks\<close>.
*)

lemma [\<phi>reason 1200]:
  \<open> \<p>\<r>\<e>\<m>\<i>\<s>\<e> Invt_Ticks current liquidity growth \<delta> ticks
\<Longrightarrow> ticks \<Ztypecolon> RawTicks \<i>\<m>\<p>\<l>\<i>\<e>\<s> (liquidity, growth) \<Ztypecolon> Ticks current \<delta>\<close>
  \<medium_left_bracket> construct\<phi> \<open>(liquidity, growth) \<Ztypecolon> Ticks current \<delta>\<close> \<medium_right_bracket>. .

lemma [\<phi>reason 1200]:
  \<open> \<p>\<r>\<e>\<m>\<i>\<s>\<e> Invt_Ticks current liquidity growth \<delta> ticks
\<Longrightarrow> ticks \<Ztypecolon> RawTicks \<i>\<m>\<p>\<l>\<i>\<e>\<s> (liquidity, growth) \<Ztypecolon> Ticks current \<delta>
    @action to (Ticks current \<delta>)\<close> \<medium_left_bracket> \<medium_right_bracket>. .

lemma [\<phi>reason 3000]:
  \<open> (liquidity, growth) \<Ztypecolon> Ticks current \<delta> \<i>\<m>\<p>\<l>\<i>\<e>\<s> ticks \<Ztypecolon> RawTicks \<s>\<u>\<b>\<j> ticks. Invt_Ticks current liquidity growth \<delta> ticks
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
and op_get_tickCumulative :: \<open>(VAL, VAL) proc'\<close>
and op_set_tickCumulative :: \<open>(VAL \<times> VAL, VAL) proc'\<close>
and op_get_secondsPerLiquidity :: \<open>(VAL, VAL) proc'\<close>
and op_set_secondsPerLiquidity :: \<open>(VAL \<times> VAL, VAL) proc'\<close>
and op_get_seconds :: \<open>(VAL, VAL) proc'\<close>
and op_set_seconds :: \<open>(VAL \<times> VAL, VAL) proc'\<close>
assumes
    get_liquidityGross_\<phi>app[\<phi>synthesis 1200]:
      \<open> \<p>\<r>\<o>\<c> op_get_liquidityGross ri \<lbrace> f \<Ztypecolon> RawTicks\<heavy_comma> i \<Ztypecolon> \<v>\<a>\<l>[ri] Tick
                                   \<longmapsto> f \<Ztypecolon> RawTicks\<heavy_comma> (liquidityGross o f) i \<Ztypecolon> \<v>\<a>\<l> \<int> \<rbrace>\<close>
                                                    (* to prevent higher-order unification! *)
and set_liquidityGross_\<phi>app:
      \<open> \<p>\<r>\<o>\<c> op_set_liquidityGross (rv\<^bold>, ri)
            \<lbrace> f \<Ztypecolon> RawTicks\<heavy_comma> i \<Ztypecolon> \<v>\<a>\<l>[ri] Tick \<heavy_comma> v \<Ztypecolon> \<v>\<a>\<l>[rv] \<int>
                \<longmapsto> f(i := map_liquidityGross (\<lambda>_. v) (f i)) \<Ztypecolon> RawTicks\<heavy_comma> i \<Ztypecolon> \<v>\<a>\<l> Tick \<rbrace>\<close>
and get_liquidityNet_\<phi>app[\<phi>synthesis 1200]:
      \<open> \<p>\<r>\<o>\<c> op_get_liquidityNet ri
            \<lbrace> f \<Ztypecolon> RawTicks\<heavy_comma> i \<Ztypecolon> \<v>\<a>\<l>[ri] Tick
                \<longmapsto> f \<Ztypecolon> RawTicks\<heavy_comma> (liquidityNet o f) i \<Ztypecolon> \<v>\<a>\<l> \<int> \<rbrace>\<close>
and set_liquidityNet_\<phi>app:
      \<open> \<p>\<r>\<o>\<c> op_set_liquidityNet (rv\<^bold>, ri)
            \<lbrace> f \<Ztypecolon> RawTicks\<heavy_comma> i \<Ztypecolon> \<v>\<a>\<l>[ri] Tick \<heavy_comma> v \<Ztypecolon> \<v>\<a>\<l>[rv] \<int>
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
and get_tickCumulative_\<phi>app[\<phi>synthesis 1200]:
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

abbreviation gSum where \<open>gSum growth \<equiv> (\<Sum>x = MIN_TICK-1..MAX_TICK. growth x)\<close>

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

abbreviation \<open>next_initialized \<delta> i j \<equiv> (\<forall>k. i < k \<and> k < j \<longrightarrow> \<delta> k = None)\<close>



context Tick_spec begin

proc getFeeGrowthInside:
  premises \<open>\<delta> lower \<noteq> None\<close> and \<open>\<delta> upper \<noteq> None\<close> (*They mean the upper tick and the lower tick is initialized*)
    and    \<open>lower < upper\<close>
  premises \<open>global_fee0 = growth.fee0 (gSum growth)\<close> (*global_fee0 is the sum of all the growth at every ticks*)
    and    \<open>global_fee1 = growth.fee1 (gSum growth)\<close>
  input \<open>(liq, growth) \<Ztypecolon> Ticks current \<delta> \<heavy_comma>
          lower \<Ztypecolon> \<v>\<a>\<l> Tick \<heavy_comma> upper \<Ztypecolon> \<v>\<a>\<l> Tick \<heavy_comma> current \<Ztypecolon> \<v>\<a>\<l> Tick \<heavy_comma> global_fee0 \<Ztypecolon> \<v>\<a>\<l> \<real> \<heavy_comma> global_fee1 \<Ztypecolon> \<v>\<a>\<l> \<real>\<close>
  output \<open>(liq, growth) \<Ztypecolon> Ticks current \<delta> \<heavy_comma>
          growth.fee0 (sum growth {lower..<upper} - the (\<delta> lower) + the (\<delta> upper)) \<Ztypecolon> \<v>\<a>\<l> \<real> \<heavy_comma>
          growth.fee1 (sum growth {lower..<upper} - the (\<delta> lower) + the (\<delta> upper)) \<Ztypecolon> \<v>\<a>\<l> \<real>\<close>
  is [routine_basic]
  \<medium_left_bracket> to \<open>RawTicks\<close> ;;

    obtain \<delta>_lower \<delta>_upper where \<delta>_lower[simp]: \<open>\<delta> lower = Some \<delta>_lower\<close>
                            and \<delta>_upper[simp]: \<open>\<delta> upper = Some \<delta>_upper\<close>
      using the_\<phi>(2) the_\<phi>(3) by blast
    
    note lower_simps[simp] =
          \<open>Invt_Ticks current liq growth \<delta> ticks\<close>[unfolded Invt_Ticks_def Invt_A_Tick_def
                  growth_outside_def, THEN conjunct1, THEN spec[where x=lower], simplified]
    note upper_simps[simp] =
          \<open>Invt_Ticks current liq growth \<delta> ticks\<close>[unfolded Invt_Ticks_def Invt_A_Tick_def
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

proc cross:
  premises \<open>\<delta> i \<noteq> None\<close>
    and    \<open>if j < i then next_initialized \<delta> j i else next_initialized \<delta> (i-1) j\<close>
  premises \<open>fee0 = growth.fee0 (gSum growth)\<close> (*global_fee0 is the sum of all the growth at every ticks*)
    and    \<open>fee1 = growth.fee1 (gSum growth)\<close>
    and    \<open>sec_per_liq = growth.secondsPerLiquidity (gSum growth)\<close>
    and    \<open>tick_cumu = growth.tickCumulative (gSum growth)\<close>
    and    \<open>time = growth.seconds (gSum growth)\<close>
  input  \<open>(liq, growth) \<Ztypecolon> Ticks j \<delta> \<heavy_comma> i \<Ztypecolon> \<v>\<a>\<l> Tick \<heavy_comma> fee0 \<Ztypecolon> \<v>\<a>\<l> \<real> \<heavy_comma> fee1 \<Ztypecolon> \<v>\<a>\<l> \<real> \<heavy_comma>
           sec_per_liq \<Ztypecolon> \<v>\<a>\<l> \<real>\<heavy_comma> tick_cumu \<Ztypecolon> \<v>\<a>\<l> \<int> \<heavy_comma> time \<Ztypecolon> \<v>\<a>\<l> \<int>\<close>
  output \<open>(liq, growth) \<Ztypecolon> Ticks (if j < i then i else i - 1) \<delta> \<close>
  is [routine]
  \<medium_left_bracket> to \<open>RawTicks\<close> \<exists>ticks
  obtain fee0' fee1' spl' tc' time' liqG' liqN' init'
    where Tick_i[simp]: \<open>ticks i = tick_info (fee0', fee1', spl', tc', time') liqG' liqN' init'\<close>
    by (metis surj_pair tick_info.exhaust)

  ;; $i set_feeGrowth0 ($fee0 sub ($i get_feeGrowth0))
        set_feeGrowth1 ($fee1 sub ($i get_feeGrowth1))
        set_secondsPerLiquidity ($sec_per_liq sub ($i get_secondsPerLiquidity))
        set_tickCumulative ($tick_cumu sub ($i get_tickCumulative))
        set_seconds ($time sub ($i get_seconds)) ;;

  have th1[simp]:
        \<open>\<And>A. (growth.fee0 A - fee0', growth.fee1 A - fee1', growth.tickCumulative A - spl',
              growth.secondsPerLiquidity A - tc', growth.seconds A - time')
          = A - (fee0', fee1', spl', tc', time')\<close>
    by (case_tac A; simp)
  note th2 = \<open>Invt_Ticks j liq growth \<delta> ticks\<close>[unfolded Invt_Ticks_def Invt_A_Tick_def]
  note th3 = th2[THEN conjunct1]

  \<medium_right_bracket> unfolding Invt_Ticks_def Invt_A_Tick_def
    using th2 th3[THEN spec[where x=i]] Tick_i the_\<phi>(2,3) the_\<phi>lemmata(1)
    apply (auto)
    apply (smt (verit) th3 growth_outside_shift_mono option.pred_inject(1) option.pred_inject(2))
    by (smt (verit) growth_outside_def option.pred_inject(1) option.pred_inject(2) th3)
    .

end

end