theory UniSWP_Position
  imports UniSWP_Common
begin

no_notation inter (infixl "Int" 70)
        and union (infixl "Un" 65)
        and Nats  ("\<nat>")
        and Ints  ("\<int>")

section \<open>Semantics\<close>

subsection \<open>Position Value\<close>

datatype pos = pos
  (address: address)
  (lower: tick)
  (upper: tick)

hide_const (open) address lower upper pos

subsection \<open>Position Info\<close>

datatype pos_info = pos_info
  (liquidity: token)
  (last_fee0: fee)
  (last_fee1: fee)
  (deposit0: fee)
  (deposit1: fee)

setup \<open>Sign.mandatory_path "pos_info"\<close>

definition \<open>map_liquidity F x = (case x of pos_info l f1 f2 d1 d2 \<Rightarrow> pos_info (F l) f1 f2 d1 d2)\<close>
lemma [simp]: \<open>pos_info.map_liquidity F (pos_info l f1 f2 d1 d2) = (pos_info (F l) f1 f2 d1 d2)\<close>
  unfolding pos_info.map_liquidity_def by simp

definition \<open>map_last_fee0 F x = (case x of pos_info l f1 f2 d1 d2 \<Rightarrow> pos_info l (F f1) f2 d1 d2)\<close>
lemma [simp]: \<open>pos_info.map_last_fee0 F (pos_info l f1 f2 d1 d2) = (pos_info l (F f1) f2 d1 d2)\<close>
  unfolding pos_info.map_last_fee0_def by simp

definition \<open>map_last_fee1 F x = (case x of pos_info l f1 f2 d1 d2 \<Rightarrow> pos_info l f1 (F f2) d1 d2)\<close>
lemma [simp]: \<open>pos_info.map_last_fee1 F (pos_info l f1 f2 d1 d2) = (pos_info l f1 (F f2) d1 d2)\<close>
  unfolding pos_info.map_last_fee1_def by simp

definition \<open>map_deposit0 F x = (case x of pos_info l f1 f2 d1 d2 \<Rightarrow> pos_info l f1 f2 (F d1) d2)\<close>
lemma [simp]: \<open>pos_info.map_deposit0 F (pos_info l f1 f2 d1 d2) = (pos_info l f1 f2 (F d1) d2)\<close>
  unfolding pos_info.map_deposit0_def by simp

definition \<open>map_deposit1 F x = (case x of pos_info l f1 f2 d1 d2 \<Rightarrow> pos_info l f1 f2 d1 (F d2))\<close>
lemma [simp]: \<open>pos_info.map_deposit1 F (pos_info l f1 f2 d1 d2) = (pos_info l f1 f2 d1 (F d2))\<close>
  unfolding pos_info.map_deposit1_def by simp


setup \<open>Sign.parent_path\<close>

hide_const (open) liquidity last_fee0 last_fee1 deposit0 deposit1

type_synonym positions = \<open>pos \<Rightarrow> pos_info\<close>
type_synonym apositions = \<open>pos \<Rightarrow> apos_info\<close>
type_synonym positions_resource = \<open>positions nosep option\<close>


(*
resource_space uswp_pos_res = \<phi>empty_res +
  R_positions :: positions_resource

debt_axiomatization R_positions :: \<open>positions_resource resource_entry\<close>
  where uswp_pos_res_ax: \<open>uswp_pos_res R_positions\<close>

interpretation uswp_pos_res R_positions using uswp_pos_res_ax .

hide_fact uswp_pos_res_ax uswp_pos_res_axioms uswp_pos_res_fields_axioms

debt_axiomatization
  res_valid_positions[simp]: \<open>Resource_Validator R_positions.name = {R_positions.inject poss |poss. True}\<close>

interpretation R_positions: nonsepable_mono_resource R_positions \<open>UNIV\<close>
  apply (standard; simp add: set_eq_iff image_iff)
  by (metis nosep.collapse not_None_eq)

subsubsection \<open>Fiction\<close>

fiction_space uswp_pos_fic :: \<open>RES_N \<Rightarrow> RES\<close> =
  FIC_positions :: \<open>R_positions.raw_basic_fiction \<F>_it\<close>

debt_axiomatization FIC_positions :: \<open>positions_resource fiction_entry\<close>
  where uswp_pos_fic_ax: \<open>uswp_pos_fic INTERPRET FIC_positions\<close>

interpretation uswp_pos_fic INTERPRET FIC_positions using uswp_pos_fic_ax .

hide_fact uswp_pos_fic_ax uswp_pos_fic_axioms

interpretation FIC_positions: identity_fiction \<open>UNIV\<close> R_positions FIC_positions
  by (standard; simp add: set_eq_iff image_iff)
*)

section \<open>\<phi>-Types - Part I - Raw\<close>

subsection \<open>Position Value\<close>

debt_axiomatization
    Pos :: \<open>(VAL, pos) \<phi>\<close>
and op_mk_pos :: \<open>(VAL \<times> VAL \<times> VAL, VAL) proc'\<close>
and op_dest_pos :: \<open>(VAL, VAL \<times> VAL \<times> VAL) proc'\<close>
where
  op_mk_pos_\<phi>app [\<phi>synthesis 1200]:
    \<open>\<p>\<r>\<o>\<c> op_mk_pos (va\<^bold>, vb\<^bold>, vc)
        \<lbrace> addr \<Ztypecolon> \<v>\<a>\<l>[vc] Address\<heavy_comma> lower \<Ztypecolon> \<v>\<a>\<l>[vb] Tick\<heavy_comma> upper \<Ztypecolon> \<v>\<a>\<l>[va] Tick
      \<longmapsto> pos addr lower upper \<Ztypecolon> \<v>\<a>\<l> Pos\<rbrace>\<close>
and op_dest_pos_\<phi>app:
    \<open>\<p>\<r>\<o>\<c> op_dest_pos v
        \<lbrace> pos addr lower upper \<Ztypecolon> \<v>\<a>\<l>[v] Pos
      \<longmapsto> addr \<Ztypecolon> \<v>\<a>\<l> Address\<heavy_comma> lower \<Ztypecolon> \<v>\<a>\<l> Tick\<heavy_comma> upper \<Ztypecolon> \<v>\<a>\<l> Tick\<rbrace>\<close>



subsection \<open>Position Info\<close>

debt_axiomatization RawPositions :: \<open>(fiction, pos \<Rightarrow> pos_info option) \<phi>\<close>

abbreviation RawPosition :: \<open>pos \<Rightarrow> (fiction, pos_info) \<phi>\<close>
  where \<open>RawPosition k \<equiv> (RawPositions \<Zcomp> k \<^bold>\<rightarrow> \<black_circle> Identity)\<close>

lemma [\<phi>reason 1200]:
  \<open>1(pos \<mapsto> info) \<Ztypecolon> RawPositions \<i>\<m>\<p>\<l>\<i>\<e>\<s> info \<Ztypecolon> RawPosition pos\<close>
  \<medium_left_bracket> \<medium_right_bracket>. .

lemma [\<phi>reason 1200]:
  \<open>info \<Ztypecolon> RawPosition pos \<i>\<m>\<p>\<l>\<i>\<e>\<s> 1(pos \<mapsto> info) \<Ztypecolon> RawPositions\<close>
  \<medium_left_bracket> \<medium_right_bracket>. .


(*definition Abstract_Sep :: \<open>('c::sep_magma,'a::sep_magma) \<phi> \<Rightarrow> bool\<close>
  where \<open>Abstract_Sep T \<longleftrightarrow> (\<forall>x y. x ## y \<longrightarrow> (x * y \<Ztypecolon> T) = (x \<Ztypecolon> T) * (y \<Ztypecolon> T))\<close>

definition Sep_Functor :: \<open>(('cc::sep_magma, 'aa::sep_magma) \<phi> \<Rightarrow> ('c::sep_magma,'a::sep_magma) \<phi>) \<Rightarrow> bool\<close>
  where \<open>Sep_Functor F \<longleftrightarrow> (\<forall>T. Abstract_Sep T \<longrightarrow> Abstract_Sep (F T))\<close>

lemma
  \<open>Sep_Functor F \<Longrightarrow> Abstract_Sep T \<Longrightarrow> x ## y \<Longrightarrow> ((x * y) \<Ztypecolon> F T) = (x \<Ztypecolon> F T) * (y \<Ztypecolon> F T) \<close>
  unfolding Sep_Functor_def Abstract_Sep_def
  by blast
*)

definition Invt_Position :: \<open>growths \<Rightarrow> pos \<Rightarrow> pos_info \<Rightarrow> apos_info \<Rightarrow> bool\<close>
  where \<open>Invt_Position growths p pi ap
     \<longleftrightarrow> apos_info.revenue0 ap - apos_info.withdrawn0 ap = pos_info.deposit0 pi + pos_info.liquidity pi * (growth.fee0 (\<Sum>i = pos.lower p ..< pos.upper p. growths i) - pos_info.last_fee0 pi)
      \<and> apos_info.revenue1 ap - apos_info.withdrawn1 ap = pos_info.deposit1 pi + pos_info.liquidity pi * (growth.fee1 (\<Sum>i = pos.lower p ..< pos.upper p. growths i) - pos_info.last_fee1 pi)\<close>

definition Invt_Positions :: \<open>growths \<Rightarrow> positions \<Rightarrow> apositions \<Rightarrow> bool\<close>
  where \<open>Invt_Positions growths ps aps
    \<longleftrightarrow> (\<forall>p. Invt_Position growths p (ps p) (aps p))\<close>

definition updated_positions :: \<open>positions \<Rightarrow> apositions \<Rightarrow> bool\<close>
  where \<open>updated_positions ps aps
    \<longleftrightarrow> (\<forall>p. apos_info.revenue0 (aps p) - apos_info.withdrawn0 (aps p) = pos_info.deposit0 (ps p) )
      \<and> (\<forall>p. apos_info.revenue1 (aps p) - apos_info.withdrawn1 (aps p) = pos_info.deposit1 (ps p) )\<close>

definition Position :: \<open>growths \<Rightarrow> pos \<Rightarrow> (fiction, apos_info) \<phi>\<close>
  where [\<phi>defs]: \<open>Position growths p aps =
    (pos \<Ztypecolon> RawPosition p \<s>\<u>\<b>\<j> pos. Invt_Position growths p pos aps)\<close>

term Fun
thm Func_def
term \<open>RawPositions \<Zcomp> (Identity \<Rrightarrow> XX)\<close>

definition Updated_Positions :: \<open>growths \<Rightarrow> (fiction, apositions) \<phi>\<close>
  where [\<phi>defs]: \<open>Updated_Positions growths aps =
    (ps \<Ztypecolon> RawPositions \<s>\<u>\<b>\<j> ps. Invt_Positions growths ps aps \<and> updated_positions ps aps)\<close>

definition Positions :: \<open>growths \<Rightarrow> (fiction, apositions) \<phi>\<close>
  where [\<phi>defs]: \<open>Positions growths aps =
    (ps \<Ztypecolon> RawPositions \<s>\<u>\<b>\<j> ps. Invt_Positions growths ps aps)\<close>

lemma [\<phi>reason 1200]:
  \<open>aps \<Ztypecolon> Updated_Positions growths \<i>\<m>\<p>\<l>\<i>\<e>\<s> ps \<Ztypecolon> RawPositions \<s>\<u>\<b>\<j> ps. Invt_Positions growths ps aps \<and> updated_positions ps aps
   @action to RawPositions\<close>
  \<medium_left_bracket> destruct\<phi> _ \<medium_right_bracket>. .

lemma [\<phi>reason 1200]:
  \<open>aps \<Ztypecolon> Positions growths \<i>\<m>\<p>\<l>\<i>\<e>\<s> ps \<Ztypecolon> RawPositions \<s>\<u>\<b>\<j> ps. Invt_Positions growths ps aps
   @action to RawPositions\<close>
  \<medium_left_bracket> destruct\<phi> _ \<medium_right_bracket>. .

lemma [\<phi>reason 1200]:
  \<open> \<p>\<r>\<e>\<m>\<i>\<s>\<e> Invt_Positions growths ps aps \<and> updated_positions ps aps
\<Longrightarrow> ps \<Ztypecolon> RawPositions \<i>\<m>\<p>\<l>\<i>\<e>\<s> aps \<Ztypecolon> Updated_Positions growths\<close>
  \<medium_left_bracket> construct\<phi> \<open>aps \<Ztypecolon> Updated_Positions growths\<close> \<medium_right_bracket>. .

lemma [\<phi>reason 1200]:
  \<open> \<p>\<r>\<e>\<m>\<i>\<s>\<e> Invt_Positions growths ps aps
\<Longrightarrow> ps \<Ztypecolon> RawPositions \<i>\<m>\<p>\<l>\<i>\<e>\<s> aps \<Ztypecolon> Positions growths\<close>
  \<medium_left_bracket> construct\<phi> \<open>aps \<Ztypecolon> Positions growths\<close> \<medium_right_bracket>. .

lemma [\<phi>reason 1200]:
  \<open>aps \<Ztypecolon> Updated_Positions growths \<i>\<m>\<p>\<l>\<i>\<e>\<s> aps \<Ztypecolon> Positions growths\<close>
  \<medium_left_bracket> to \<open>RawPositions\<close> \<medium_right_bracket>. .

lemma [\<phi>reason 1200]:
  \<open>aps \<Ztypecolon> Updated_Positions growths \<i>\<m>\<p>\<l>\<i>\<e>\<s> aps \<Ztypecolon> Positions growths
   @action to (Positions growths)\<close> \<medium_left_bracket> \<medium_right_bracket>. .


section \<open>Axiomatic Semantics of Abstract Operations\<close>

debt_axiomatization
    op_get_liquidity :: \<open>(VAL, VAL) proc'\<close>
and op_set_liquidity :: \<open>(VAL \<times> VAL, unit) proc'\<close>
and op_get_last_fee0 :: \<open>(VAL, VAL) proc'\<close>
and op_set_last_fee0 :: \<open>(VAL \<times> VAL, unit) proc'\<close>
and op_get_last_fee1 :: \<open>(VAL, VAL) proc'\<close>
and op_set_last_fee1 :: \<open>(VAL \<times> VAL, unit) proc'\<close>
and op_get_deposti0 :: \<open>(VAL, VAL) proc'\<close>
and op_set_deposti0 :: \<open>(VAL \<times> VAL, unit) proc'\<close>
and op_get_deposti1 :: \<open>(VAL, VAL) proc'\<close>
and op_set_deposti1 :: \<open>(VAL \<times> VAL, unit) proc'\<close>
where
  op_get_liquidity_\<phi>app:
    \<open>\<p>\<r>\<o>\<c> op_get_liquidity ri
        \<lbrace> ps \<Ztypecolon> RawPositions\<heavy_comma> p \<Ztypecolon> \<v>\<a>\<l>[ri] Pos \<longmapsto>
          ps \<Ztypecolon> RawPositions\<heavy_comma> (pos_info.liquidity o ps) p \<Ztypecolon> \<v>\<a>\<l> \<int> \<rbrace>\<close>
and op_set_liquidity_\<phi>app:
    \<open>\<p>\<r>\<o>\<c> op_set_liquidity (ri\<^bold>, rv)
        \<lbrace> ps \<Ztypecolon> RawPositions\<heavy_comma> p \<Ztypecolon> \<v>\<a>\<l>[ri] Pos\<heavy_comma> v \<Ztypecolon> \<v>\<a>\<l>[rv] \<int> \<longmapsto>
          ps(p := pos_info.map_liquidity (\<lambda>_. v) (ps p)) \<Ztypecolon> RawPositions \<rbrace>\<close>
and op_get_last_fee0_\<phi>app:
    \<open>\<p>\<r>\<o>\<c> op_get_last_fee0 ri
        \<lbrace> ps \<Ztypecolon> RawPositions\<heavy_comma> p \<Ztypecolon> \<v>\<a>\<l>[ri] Pos \<longmapsto>
          ps \<Ztypecolon> RawPositions\<heavy_comma> (pos_info.last_fee0 o ps) p \<Ztypecolon> \<v>\<a>\<l> \<real> \<rbrace>\<close>
and op_set_last_fee0_\<phi>app:
    \<open>\<p>\<r>\<o>\<c> op_set_last_fee0 (ri\<^bold>, rv)
        \<lbrace> ps \<Ztypecolon> RawPositions\<heavy_comma> p \<Ztypecolon> \<v>\<a>\<l>[ri] Pos\<heavy_comma> r \<Ztypecolon> \<v>\<a>\<l>[rv] \<real> \<longmapsto>
          ps(p := pos_info.map_last_fee0 (\<lambda>_. r) (ps p)) \<Ztypecolon> RawPositions \<rbrace>\<close>
and op_get_last_fee1_\<phi>app:
    \<open>\<p>\<r>\<o>\<c> op_get_last_fee1 ri
        \<lbrace> ps \<Ztypecolon> RawPositions\<heavy_comma> p \<Ztypecolon> \<v>\<a>\<l>[ri] Pos \<longmapsto>
          ps \<Ztypecolon> RawPositions\<heavy_comma> (pos_info.last_fee1 o ps) p \<Ztypecolon> \<v>\<a>\<l> \<real> \<rbrace>\<close>
and op_set_last_fee1_\<phi>app:
    \<open>\<p>\<r>\<o>\<c> op_set_last_fee1 (ri\<^bold>, rv)
        \<lbrace> ps \<Ztypecolon> RawPositions\<heavy_comma> p \<Ztypecolon> \<v>\<a>\<l>[ri] Pos\<heavy_comma> r \<Ztypecolon> \<v>\<a>\<l>[rv] \<real> \<longmapsto>
          ps(p := pos_info.map_last_fee1 (\<lambda>_. r) (ps p)) \<Ztypecolon> RawPositions \<rbrace>\<close>
and op_get_deposit0_\<phi>app:
    \<open>\<p>\<r>\<o>\<c> op_get_deposit0 ri
        \<lbrace> ps \<Ztypecolon> RawPositions\<heavy_comma> p \<Ztypecolon> \<v>\<a>\<l>[ri] Pos \<longmapsto>
          ps \<Ztypecolon> RawPositions\<heavy_comma> (pos_info.deposit0 o ps) p \<Ztypecolon> \<v>\<a>\<l> \<real> \<rbrace>\<close>
and op_set_deposit0_\<phi>app:
    \<open>\<p>\<r>\<o>\<c> op_set_deposit0 (ri\<^bold>, rv)
        \<lbrace> ps \<Ztypecolon> RawPositions\<heavy_comma> p \<Ztypecolon> \<v>\<a>\<l>[ri] Pos\<heavy_comma> r \<Ztypecolon> \<v>\<a>\<l>[rv] \<real> \<longmapsto>
          ps(p := pos_info.map_deposit0 (\<lambda>_. r) (ps p)) \<Ztypecolon> RawPositions \<rbrace>\<close>
and op_get_deposit1_\<phi>app:
    \<open>\<p>\<r>\<o>\<c> op_get_deposit1 ri
        \<lbrace> ps \<Ztypecolon> RawPositions\<heavy_comma> p \<Ztypecolon> \<v>\<a>\<l>[ri] Pos \<longmapsto>
          ps \<Ztypecolon> RawPositions\<heavy_comma> (pos_info.deposit1 o ps) p \<Ztypecolon> \<v>\<a>\<l> \<real> \<rbrace>\<close>
and op_set_deposit1_\<phi>app:
    \<open>\<p>\<r>\<o>\<c> op_set_deposit1 (ri\<^bold>, rv)
        \<lbrace> ps \<Ztypecolon> RawPositions\<heavy_comma> p \<Ztypecolon> \<v>\<a>\<l>[ri] Pos\<heavy_comma> r \<Ztypecolon> \<v>\<a>\<l>[rv] \<real> \<longmapsto>
          ps(p := pos_info.map_deposit1 (\<lambda>_. r) (ps p)) \<Ztypecolon> RawPositions \<rbrace>\<close>


proc update:
  input \<open>\<close>
  output \<open>Void\<close>





end