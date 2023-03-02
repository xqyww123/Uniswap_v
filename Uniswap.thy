theory Uniswap
  imports Phi_Semantics.PhiSem_Machine_Integer
          Phi_Semantics.PhiSem_CF_Basic
          Phi_Semantics.PhiSem_Variable HOL.Transcendental
begin

consts Tick  :: \<open>(VAL, int) \<phi>\<close>
       Price :: \<open>(VAL, real) \<phi>\<close>

definition \<open>FACTOR = (1.0001::real)\<close>

lemma FACTOR_LG_1: \<open>1 < FACTOR\<close> unfolding FACTOR_def by simp

definition price_of :: \<open>int \<Rightarrow> real\<close>
  where price_of_def': \<open>price_of tick = sqrt (FACTOR powr (of_int tick))\<close>

lemma price_of_def: \<open>price_of t = FACTOR powr (of_int t / 2)\<close>
  unfolding price_of_def'
  by (simp add: powr_half_sqrt[symmetric] powr_powr)

hide_fact price_of_def'

lemma price_of_mono': \<open>mono price_of\<close>
  unfolding price_of_def mono_on_def
  by (simp add: FACTOR_LG_1)

lemma price_of_smono': \<open>strict_mono price_of\<close>
  unfolding price_of_def strict_mono_on_def
  by (simp add: FACTOR_LG_1)

lemma price_of_mono:
  \<open>price_of x \<le> price_of y \<longleftrightarrow> x \<le> y\<close>
  using price_of_mono'
  by (simp add: price_of_smono' strict_mono_less_eq) 

lemma price_of_smono:
  \<open>price_of x < price_of y \<longleftrightarrow> x < y\<close>
  using price_of_smono' using strict_mono_less by blast

definition \<open>tick_of_price p = (@t. price_of t \<le> p \<and> p < price_of (t+1)) \<close>

lemma tick_of_price: \<open>tick_of_price (price_of t) = t\<close>
  unfolding tick_of_price_def
  by (smt (z3) price_of_smono some_eq_imp)

lemma price_of_tick:
  assumes \<open>0 < p\<close>
  shows \<open>price_of (tick_of_price p) \<le> p \<and> p < price_of (tick_of_price p + 1)\<close>
proof -
  have \<open>\<exists>t. p < FACTOR powr t\<close>
    by (metis FACTOR_LG_1 dual_order.strict_trans floor_log_eq_powr_iff linorder_neqE_linordered_idom zero_less_one)
  then have \<open>\<exists>t. p < price_of t\<close>
    unfolding price_of_def
    by (meson FACTOR_LG_1 dual_order.strict_trans ex_less_of_int less_divide_eq_numeral1(1) powr_less_cancel_iff)
  moreover have \<open>\<exists>t. FACTOR powr t \<le> p\<close>
    using \<open>0 < p\<close> FACTOR_LG_1 floor_log_eq_powr_iff by blast
  then have \<open>\<exists>t. price_of t \<le> p\<close>
    proof -
      have \<open>\<And>x. \<exists>t. real_of_int t / 2 < x\<close> by (simp add: ex_of_int_less)
      then show ?thesis
      unfolding price_of_def
      by (meson FACTOR_LG_1 \<open>\<exists>t. FACTOR powr t \<le> p\<close> dual_order.trans less_le_not_le powr_le_cancel_iff)
    qed
  ultimately have X: \<open>(\<exists>t. price_of t \<le> p \<and> p < price_of (t+1))\<close>
    proof -
    obtain t1 where t1: \<open>price_of t1 \<le> p\<close> using \<open>\<exists>t. price_of t \<le> p\<close> by blast
    obtain t2 where t2: \<open>p < price_of t2\<close> using \<open>\<exists>t. p < price_of t\<close> by blast
    have le: \<open>t1 < t2\<close> using t1 t2 price_of_smono by fastforce
    thm int_gr_induct[OF le]
    have \<open>p < price_of t2 \<longrightarrow> ?thesis\<close>
    proof (induct rule: int_gr_induct[OF le])
      case 1
      then show ?case
        using t1 by blast
    next
      case (2 i)
      then show ?case
        by force
    qed
    then show ?thesis
      using t2 by blast
  qed
  then show ?thesis
    unfolding tick_of_price_def
    by (metis (no_types, lifting) someI_ex)
qed


debt_axiomatization getSqrtRatioAtTick :: \<open>(VAL,VAL) proc'\<close>
  where getSqrtRatioAtTick_\<phi>app:
            \<open>\<p>\<r>\<o>\<c> getSqrtRatioAtTick v \<lbrace> t \<Ztypecolon> \<v>\<a>\<l>[v] Tick \<longmapsto> price_of t \<Ztypecolon> \<v>\<a>\<l> Price \<rbrace>\<close>
    and getTickAtSqrtRatio_\<phi>app:
            \<open>\<p>\<r>\<e>\<m>\<i>\<s>\<e> 0 < p
         \<Longrightarrow> \<p>\<r>\<o>\<c> getTickAtSqrtRatio v \<lbrace> p \<Ztypecolon> \<v>\<a>\<l>[v] Price \<longmapsto> tick_of_price p \<Ztypecolon> \<v>\<a>\<l> Tick \<rbrace>\<close>

record tick_info =
  liquidityGross :: nat
  liquidityNet   :: int
  feeGrowthOutside0X128 :: nat
  feeGrowthOutside1X128 :: nat
  tickCumulativeOutside :: int
  secondsPerLiquidityOutsideX128 :: nat
  secondsOutside :: nat
  initialized :: bool

definition \<open>growth_Inv f f' delta current =
  (\<forall>(i::int). f i = (if i \<le> current then (sum f' {j. j \<le> i}) + delta i
                             else (sum f' {j. i < j}) - delta i))\<close>
  

term sum


debt_axiomatization TickInfos :: \<open>(assn, int \<Rightarrow> tick_info nonsepable option) \<phi>\<close>
  where TickInfos_mult: \<open>(f1 \<Ztypecolon> TickInfos) * (f2 \<Ztypecolon> TickInfos) = (f1 * f2 \<Ztypecolon> TickInfos)\<close>
          \<comment> \<open>Separation of Abstraction ?! cool! \<close>

thm TickInfos_mult

definition TickInfo


debt_axiomatization get_TickInfo :: \<open>(VAL,VAL) proc'\<close>
  where getSqrtRatioAtTick_\<phi>app:
            \<open>\<p>\<r>\<o>\<c> getSqrtRatioAtTick v \<lbrace> t \<Ztypecolon> \<v>\<a>\<l>[v] Tick \<longmapsto> price_of t \<Ztypecolon> \<v>\<a>\<l> Price \<rbrace>\<close>
    and getTickAtSqrtRatio_\<phi>app:
            \<open>\<p>\<r>\<e>\<m>\<i>\<s>\<e> 0 < p
         \<Longrightarrow> \<p>\<r>\<o>\<c> getTickAtSqrtRatio v \<lbrace> p \<Ztypecolon> \<v>\<a>\<l>[v] Price \<longmapsto> tick_of_price p \<Ztypecolon> \<v>\<a>\<l> Tick \<rbrace>\<close>


definition \<open>Ticks = (\<lambda>info. into \<Ztypecolon> TickInfo' \<s>\<u>\<b>\<j>  )\<close>


end