theory Uniswap_Virtual_Resource
  imports Phi_Semantics.PhiSem_Int_ArbiPrec HOL.Real
          Phi_Semantics.PhiSem_Real_Abst
          Phi_Semantics.PhiSem_CF_Routine
begin

no_notation inter (infixl "Int" 70)
        and union (infixl "Un" 65)
        and Nats  ("\<nat>")
        and Ints  ("\<int>")

section \<open>Semantics\<close>

subsection \<open>Models\<close>

subsubsection \<open>Virtual Resources\<close>

(*
record growth =
  fee0 :: real
  fee1 :: real
  tickCumulative :: int
  secondsPerLiquidity :: real
  secondsOutside :: int *)

thm plus_prod_def
value \<open>(2::nat, 3::int) + (0, 1)\<close>

type_synonym growth = \<open>real \<times> real \<times> int \<times> real \<times> int\<close>

(*We do this ugly job because prod is configured with all algebraic properties!, like ring*)

setup \<open>Sign.mandatory_path "growth"\<close>

definition \<open>fee0 (x::growth) = (case x of (a,b,c,d,e) \<Rightarrow> a)\<close>
definition \<open>map_fee0 f (x::growth) = (case x of (a,b,c,d,e) \<Rightarrow> ((f a,b,c,d,e) :: growth))\<close>
lemma [simp]: \<open>growth.fee0 (a,b,c,d,e) = a\<close> unfolding growth.fee0_def by simp
lemma [simp]: \<open>growth.map_fee0 f (a,b,c,d,e) = (f a,b,c,d,e)\<close> unfolding growth.map_fee0_def by simp

definition \<open>fee1 (x::growth) = (case x of (a,b,c,d,e) \<Rightarrow> b)\<close>
definition \<open>map_fee1 f (x::growth) = (case x of (a,b,c,d,e) \<Rightarrow> ((a,f b,c,d,e) :: growth))\<close>
lemma [simp]: \<open>growth.fee1 (a,b,c,d,e) = b\<close> unfolding growth.fee1_def by simp
lemma [simp]: \<open>growth.map_fee1 f (a,b,c,d,e) = (a,f b,c,d,e)\<close> unfolding growth.map_fee1_def by simp

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

setup \<open>Sign.parent_path\<close>

lemma fee0_plus_homo[simp]:
  \<open>growth.fee0 (a + b) = growth.fee0 a + growth.fee0 b\<close>
  by (cases a; cases b; simp)

lemma fee0_sub_homo[simp]:
  \<open>growth.fee0 (a - b) = growth.fee0 a - growth.fee0 b\<close>
  by (cases a; cases b; simp)

lemma fee0_sum[simp]:
  \<open>growth.fee0 (sum f S) = sum (growth.fee0 o f) S\<close>
  by (metis add.right_neutral add_diff_cancel_left' fee0_plus_homo sum_comp_morphism)

lemma fee1_plus_homo[simp]:
  \<open>growth.fee1 (a + b) = growth.fee1 a + growth.fee1 b\<close>
  by (cases a; cases b; simp)

lemma fee1_sub_homo[simp]:
  \<open>growth.fee1 (a - b) = growth.fee1 a - growth.fee1 b\<close>
  by (cases a; cases b; simp)

lemma fee1_sum[simp]:
  \<open>growth.fee1 (sum f S) = sum (growth.fee1 o f) S\<close>
  by (metis add.right_neutral add_diff_cancel_left' fee1_plus_homo sum_comp_morphism)


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



type_synonym tick = int
type_synonym ticks = \<open>tick \<Rightarrow> tick_info\<close>
type_synonym ticks_resource = \<open>ticks nosep option\<close>

resource_space \<phi>uniswap_res = \<phi>empty_res +
  R_ticks :: ticks_resource

debt_axiomatization R_ticks :: \<open>ticks_resource resource_entry\<close>
  where \<phi>uniswap_res_ax: \<open>\<phi>uniswap_res R_ticks\<close>

interpretation \<phi>uniswap_res R_ticks using \<phi>uniswap_res_ax .

hide_fact \<phi>uniswap_res_ax \<phi>uniswap_res_axioms \<phi>uniswap_res_fields_axioms

debt_axiomatization
  res_valid_ticks[simp]: \<open>Resource_Validator R_ticks.name =
                           {R_ticks.inject ticks |ticks. True}\<close>

interpretation R_ticks: nonsepable_mono_resource R_ticks \<open>UNIV\<close>
  apply (standard; simp add: set_eq_iff image_iff)
  by (metis nosep.collapse not_None_eq)


subsubsection \<open>Fiction\<close>

fiction_space \<phi>uniswap_fic :: \<open>RES_N \<Rightarrow> RES\<close> =
  FIC_ticks :: \<open>R_ticks.raw_basic_fiction \<F>_it\<close>

debt_axiomatization FIC_ticks :: \<open>ticks_resource fiction_entry\<close>
  where \<phi>uniswap_fic_ax: \<open>\<phi>uniswap_fic INTERPRET FIC_ticks\<close>

interpretation \<phi>uniswap_fic INTERPRET FIC_ticks using \<phi>uniswap_fic_ax .

hide_fact \<phi>uniswap_fic_ax \<phi>uniswap_fic_axioms

interpretation FIC_ticks: identity_fiction \<open>UNIV\<close> R_ticks FIC_ticks
  by (standard; simp add: set_eq_iff image_iff)


section \<open>\<phi>-Types - Part I - Raw\<close>

subsection \<open>Tick\<close>

text \<open>It is merely an integer for now, but in future it will have range restriction.\<close>

definition Tick :: \<open>(VAL, tick) \<phi>\<close> where [\<phi>defs]: \<open>Tick i = (i \<Ztypecolon> \<int>)\<close>



lemma [\<phi>reason 1200]:
  \<open> \<t>\<h>\<r>\<e>\<s>\<h>\<o>\<l>\<d> 1
\<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> i = j
\<Longrightarrow> i \<Ztypecolon> \<int> \<i>\<m>\<p>\<l>\<i>\<e>\<s> j \<Ztypecolon> Tick\<close>
  \<medium_left_bracket> construct\<phi> \<open>i \<Ztypecolon> Tick\<close> \<medium_right_bracket>. .

lemma [\<phi>reason 1200]:
  \<open>i \<Ztypecolon> \<int> \<i>\<m>\<p>\<l>\<i>\<e>\<s> i \<Ztypecolon> Tick @action to Tick\<close> \<medium_left_bracket> \<medium_right_bracket>. .

lemma [\<phi>reason 1200, \<phi>inhabitance_rule]:
  \<open> \<t>\<h>\<r>\<e>\<s>\<h>\<o>\<l>\<d> 1
\<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> i = j
\<Longrightarrow> i \<Ztypecolon> Tick \<i>\<m>\<p>\<l>\<i>\<e>\<s> j \<Ztypecolon> \<int>\<close>
  \<medium_left_bracket> destruct\<phi> _ \<medium_right_bracket>. .

lemma [\<phi>reason 1200]: \<open>i \<Ztypecolon> Tick \<i>\<m>\<p>\<l>\<i>\<e>\<s> i \<Ztypecolon> \<int> @action to \<int>\<close> \<medium_left_bracket> \<medium_right_bracket>. .

lemma [\<phi>reason 1000]: "\<phi>Equal Tick (\<lambda>x y. True) (=)" \<medium_left_bracket> to \<int> \<medium_right_bracket>. .

lemma [\<phi>reason 1000]: \<open>\<phi>SemType (x \<Ztypecolon> Tick) aint\<close> \<medium_left_bracket> to \<int> \<medium_right_bracket>. .

lemma [\<phi>reason 1000]: "\<phi>Zero aint Tick 0" \<medium_left_bracket> \<open>0 \<Ztypecolon> \<int>\<close> \<medium_right_bracket>. .





subsection \<open>Tick Info Data\<close>

type_synonym liquidity = \<open>tick \<Rightarrow> int\<close>
type_synonym growths = \<open>tick \<Rightarrow> growth\<close>
type_synonym opt_growths = \<open>tick \<Rightarrow> growth option\<close>

definition \<open>MIN_TICK = (-887272::int)\<close>
definition \<open>MAX_TICK = ( 887272::int)\<close>

lemma MIN_TICK_LT_MAX_TICK[simp]:
  \<open>MIN_TICK < MAX_TICK\<close>
  unfolding MIN_TICK_def MAX_TICK_def by simp
  

definition growth_outside :: \<open>growths \<Rightarrow> tick \<Rightarrow> growth \<Rightarrow> tick \<Rightarrow> growth\<close>
  where \<open>growth_outside abs_func tick delta current =
  (if tick \<le> current then (sum abs_func {MIN_TICK..<tick}) + delta
                      else (sum abs_func {tick..MAX_TICK}) - delta)\<close>

(*report: the spec of the tick_info.initialized is incorrect!
  it is not \<open>liquidity i \<noteq> 0\<close> 

  abst: real (physical) growth
  delta: is some if initialized.
*)
definition Invt_A_Tick :: \<open>tick \<Rightarrow> tick \<Rightarrow> liquidity
                                \<Rightarrow> growths \<Rightarrow> growth option \<Rightarrow> tick_info \<Rightarrow> bool \<close>
  where \<open>Invt_A_Tick i current liquidity abst \<delta> ti
          \<longleftrightarrow> tick_info.liquidityGross ti = liquidity i \<and>
              tick_info.liquidityNet ti = liquidity (i + 1) - liquidity i \<and>
              pred_option (\<lambda>\<delta>. tick_info.growth ti = growth_outside abst i \<delta> current) \<delta> \<and>
              tick_info.initialized ti = (\<delta> \<noteq> None)
        \<close>

definition Invt_Ticks :: \<open>tick \<Rightarrow> liquidity \<Rightarrow> growths \<Rightarrow> opt_growths
                               \<Rightarrow> ticks \<Rightarrow> bool\<close>
  where \<open>Invt_Ticks current liquidity abst \<delta> ticks
          \<longleftrightarrow> (\<forall>i. Invt_A_Tick i current liquidity abst (\<delta> i) (ticks i))\<close>

abbreviation RawTicks :: \<open>(fiction, ticks) \<phi>\<close> where \<open>RawTicks \<equiv> (FIC_ticks.\<phi> (\<black_circle> (Nosep Identity)))\<close>

definition Ticks :: \<open>tick \<Rightarrow> (fiction, (liquidity \<times> growths \<times> opt_growths)) \<phi>\<close>
  where [\<phi>defs]: \<open>Ticks current = (\<lambda>(liquidity, growth, \<delta>).
                    ticks \<Ztypecolon> RawTicks \<s>\<u>\<b>\<j> ticks. Invt_Ticks current liquidity growth \<delta> ticks)\<close>

declare [[\<phi>trace_reasoning = 1]]

(*A problem of the automatic transformation rule is,
  look, the source \<open>ticks\<close> and the target \<open>liquidity, growth, \<delta>\<close> has no common term,
  meaning if there are two \<open>ticks1 \<Ztypecolon> RawTicks\<heavy_comma> ticks2 \<Ztypecolon> RawTicks\<close>, it is impossible to determine
  which one is the desired one to be transformed, or any combination of them two.

  There is no problem if there is only one \<open>ticks \<Ztypecolon> RawTicks\<close>.
*)

lemma [\<phi>reason 1200]:
  \<open> \<p>\<r>\<e>\<m>\<i>\<s>\<e> Invt_Ticks current liquidity growth \<delta> ticks
\<Longrightarrow> ticks \<Ztypecolon> RawTicks \<i>\<m>\<p>\<l>\<i>\<e>\<s> (liquidity, growth, \<delta>) \<Ztypecolon> Ticks current\<close>
  \<medium_left_bracket> construct\<phi> \<open>(liquidity, growth, \<delta>) \<Ztypecolon> Ticks current\<close> \<medium_right_bracket>. .

lemma [\<phi>reason 1200]:
  \<open> \<p>\<r>\<e>\<m>\<i>\<s>\<e> Invt_Ticks current liquidity growth \<delta> ticks
\<Longrightarrow> ticks \<Ztypecolon> RawTicks \<i>\<m>\<p>\<l>\<i>\<e>\<s> (liquidity, growth, \<delta>) \<Ztypecolon> Ticks current
    @action to (Ticks current)\<close> \<medium_left_bracket> \<medium_right_bracket>. .

lemma [\<phi>reason 1200]:
  \<open> (liquidity, growth, \<delta>) \<Ztypecolon> Ticks current \<i>\<m>\<p>\<l>\<i>\<e>\<s> ticks \<Ztypecolon> RawTicks \<s>\<u>\<b>\<j> ticks. Invt_Ticks current liquidity growth \<delta> ticks
    @action to RawTicks\<close>
  \<medium_left_bracket> destruct\<phi> _ \<medium_right_bracket>. .


section \<open>Axiomatic Semantics of Abstract Operations\<close>

setup \<open>Sign.mandatory_path "ticks"\<close>

definition get :: \<open>(tick_info \<Rightarrow> 'a) \<Rightarrow> ticks \<Rightarrow> tick \<Rightarrow> 'a\<close>
  where \<open>get \<equiv> Fun.comp o case_option undefined o case_nosep\<close>

lemma [simp]:
  \<open> ticks i = Some x
\<Longrightarrow> ticks.get access ticks i = access (nosep.dest x)\<close>
  unfolding ticks.get_def by (cases x; simp)

lemma [simp]:
  \<open> ticks i = None
\<Longrightarrow> ticks.get access ticks i = undefined\<close>
  unfolding ticks.get_def by simp

term \<open>map_option\<close>

definition set :: \<open>('a::zero \<Rightarrow> 'a) \<Rightarrow> 'a nosep option \<Rightarrow> 'a nosep option\<close>
  where \<open>set F x = (case x of Some (nosep x') \<Rightarrow> Some (nosep (F x'))
                            | None \<Rightarrow> Some (nosep (F 0)))\<close>

lemma [simp]:
  \<open>ticks.set F (Some (nosep x)) = Some (nosep (F x))\<close>
  \<open>ticks.set F (None) = Some (nosep (F 0))\<close>
  unfolding ticks.set_def by simp_all

setup \<open>Sign.parent_path\<close>

debt_axiomatization
    op_get_liquidityGross :: \<open>(VAL, VAL) proc'\<close>
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
where
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

thm set_feeGrowth0_\<phi>app


section \<open>Verify\<close>


lemma interval_sub_1[simp]:
  \<open>A \<le> B \<and> B \<le> C \<Longrightarrow> {A..C} - {A..<B} = {B..C}\<close>
  for A :: int by auto

lemma sum_sub_1[simp]:
  \<open>A \<le> B \<and> B \<le> C \<Longrightarrow> sum f {A..C} - sum f {A..<B} = sum f {B..C}\<close>
  for f :: \<open>int \<Rightarrow> 'a::ab_group_add\<close>
  by (smt (verit, del_insts) atLeastLessThan_upto atLeastatMost_subset_iff finite_atLeastAtMost_int interval_sub_1 set_upto sum_diff)

lemma interval_sub_2[simp]:
  \<open>A \<le> B \<and> B \<le> C \<Longrightarrow> {A..C} - {B..C} = {A..<B}\<close> for A :: int by auto

lemma sum_sub_2[simp]:
  \<open>A \<le> B \<and> B \<le> C \<Longrightarrow> sum f {A..C} - sum f {B..C} = sum f {A..<B}\<close>
  for f :: \<open>int \<Rightarrow> 'a::ab_group_add\<close>
  using sum_diff interval_sub_2
  by (metis atLeastatMost_subset_iff dual_order.refl finite_atLeastAtMost_int)

abbreviation gSum where \<open>gSum growth \<equiv> (\<Sum>x = MIN_TICK..MAX_TICK. growth x)\<close>

proc getFeeGrowthInside:
  premises \<open>\<delta> lower \<noteq> None\<close> and \<open>\<delta> upper \<noteq> None\<close> (*They mean the upper tick and the lower tick is initialized*)
    and    \<open>lower < upper\<close>
    and    \<open>MIN_TICK \<le> lower\<close> and \<open>upper \<le> MAX_TICK\<close>
  premises \<open>global_fee0 = growth.fee0 (gSum growth)\<close> (*global_fee0 is the sum of all the growth at every ticks*)
    and    \<open>global_fee1 = growth.fee1 (gSum growth)\<close>
  input \<open>(liq, growth, \<delta>) \<Ztypecolon> Ticks current \<heavy_comma>
          lower \<Ztypecolon> \<v>\<a>\<l> Tick \<heavy_comma> upper \<Ztypecolon> \<v>\<a>\<l> Tick \<heavy_comma> current \<Ztypecolon> \<v>\<a>\<l> Tick \<heavy_comma> global_fee0 \<Ztypecolon> \<v>\<a>\<l> \<real> \<heavy_comma> global_fee1 \<Ztypecolon> \<v>\<a>\<l> \<real>\<close>
  output \<open>(liq, growth, \<delta>) \<Ztypecolon> Ticks current \<heavy_comma>
          growth.fee0 (sum growth {lower..<upper} - the (\<delta> lower) + the (\<delta> upper)) \<Ztypecolon> \<v>\<a>\<l> \<real> \<heavy_comma>
          growth.fee1 (sum growth {lower..<upper} - the (\<delta> lower) + the (\<delta> upper)) \<Ztypecolon> \<v>\<a>\<l> \<real>\<close>
  is [routine]
  \<medium_left_bracket> to \<open>RawTicks\<close> ;;
    obtain \<delta>_lower \<delta>_upper where \<delta>_lower[simp]: \<open>\<delta> lower = Some \<delta>_lower\<close>
                            and \<delta>_upper[simp]: \<open>\<delta> upper = Some \<delta>_upper\<close>
      using the_\<phi>(2) the_\<phi>(3) by blast

    note lower_simps[simp] =
          \<open>Invt_Ticks current liq growth \<delta> ticks\<close>[unfolded Invt_Ticks_def Invt_A_Tick_def
                  growth_outside_def, THEN spec[where x=lower], simplified]
    note upper_simps[simp] =
          \<open>Invt_Ticks current liq growth \<delta> ticks\<close>[unfolded Invt_Ticks_def Invt_A_Tick_def
                  growth_outside_def, THEN spec[where x=upper], simplified]
    note diff_diff_eq[symmetric, simp] ;;

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

    note add_diff_eq[simp] \<delta>_lower[simp del] \<delta>_upper[simp del]
    have [simp]: \<open>\<delta>_lower = the (\<delta> lower)\<close> by (simp add: \<delta>_lower)
    have [simp]: \<open>\<delta>_upper = the (\<delta> upper)\<close> by (simp add: \<delta>_upper) ;;
      
    \<open>$global_fee0 - $fee0_below - $fee0_above\<close>
    \<open>$global_fee1 - $fee1_below - $fee1_above\<close>
  \<medium_right_bracket>.

proc cross:
  premises C: \<open>current = i\<close>
  input  \<open>(liq, growth, \<delta>) \<Ztypecolon> Ticks current \<heavy_comma> i \<Ztypecolon> \<v>\<a>\<l> Tick \<heavy_comma> fee0 \<Ztypecolon> \<v>\<a>\<l> \<real> \<heavy_comma> fee1 \<Ztypecolon> \<v>\<a>\<l> \<real> \<heavy_comma>
           sec_per_liq \<Ztypecolon> \<v>\<a>\<l> \<real>\<heavy_comma> tick_cumu \<Ztypecolon> \<v>\<a>\<l> \<int> \<heavy_comma> time \<Ztypecolon> \<v>\<a>\<l> \<int>\<close>
  output \<open>(liq, growth(i := (fee0, fee1, tick_cumu, sec_per_liq, time)), \<delta>) \<Ztypecolon> Ticks (current + 1)\<heavy_comma>
          liq (i + 1) - liq i \<Ztypecolon> \<v>\<a>\<l> \<int>\<close>
  is [routine]
  \<medium_left_bracket> to \<open>RawTicks\<close>
  obtain fee0' fee1' spl' tc' time' liqG' liqN' init'
    where Tick_i[simp]: \<open>ticks i = tick_info (fee0', fee1', spl', tc', time') liqG' liqN' init'\<close>
    by (metis surj_pair tick_info.exhaust)
  ;; $i set_feeGrowth0 ($fee0 sub ($i get_feeGrowth0))
     $i set_feeGrowth1 ($fee1 sub ($i get_feeGrowth1))
     $i set_secondsPerLiquidity ($sec_per_liq sub ($i get_secondsPerLiquidity))
     $i set_tickCumulative ($tick_cumu sub ($i get_tickCumulative))
     $i set_seconds ($time sub ($i get_seconds))
  ;; $i get_liquidityNet
  \<medium_right_bracket> unfolding Invt_Ticks_def Invt_A_Tick_def
    using the_\<phi>(3)[unfolded Invt_Ticks_def Invt_A_Tick_def] Tick_i
    apply auto
    apply (metis Tick_i tick_info.sel(2))
    apply (metis Tick_i tick_info.sel(3))
        apply (cases \<open>\<delta> i\<close>; clarsimp simp add: growth_outside_def)
    apply (auto simp add: C)[1]



    thm \<phi>
    thm 
  
  

  thm get_secondsPerLiquidity


(* $i set_feeGrowth0 ( $fee0 sub (get_feeGrowth0 $i), $x add ($y) ) *)

  ;; $i $fee0 $i get_feeGrowth0 - set_feeGrowth0
  ;; \<open>(growth.fee0 \<circ> tick_info.growth \<circ> ticks) ($i)\<close>

  thm \<phi>


end