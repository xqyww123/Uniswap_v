theory UniSWP_TickBitmap
  imports UniSWP_Common
begin

(*will be a good case to test our \<phi>-type-fiction conversion.
Get fiction relation from \<phi>-type relation.*)

type_synonym tick_map = \<open>tick \<Rightarrow> bool\<close>

locale Tickmap_spec =
  fixes Tickmap :: \<open>(fiction, tick_map) \<phi>\<close>
    and op_get_tickmap :: \<open>(VAL, VAL) proc'\<close>
    and nextInitializedTickWithinOneWord :: \<open>(VAL \<times> VAL, VAL \<times> VAL) proc'\<close>
  assumes op_get_tickmap_\<phi>app:
    \<open> \<p>\<r>\<o>\<c> op_get_tickmap ri \<lbrace> m \<Ztypecolon> Tickmap\<heavy_comma> i \<Ztypecolon> \<v>\<a>\<l>[ri] Tick
                          \<longmapsto> m \<Ztypecolon> Tickmap\<heavy_comma> m i \<Ztypecolon> \<v>\<a>\<l> \<bool>\<rbrace> \<close>
  and nextInitializedTickWithinOneWord_\<phi>app:
    (*we don't consider TickSpacing in this abstract specification.*)
    \<open> \<p>\<r>\<o>\<c> nextInitializedTickWithinOneWord (rlte\<^bold>, ri)
          \<lbrace> m \<Ztypecolon> Tickmap\<heavy_comma> i \<Ztypecolon> \<v>\<a>\<l>[ri] \<int>\<heavy_comma> lte \<Ztypecolon> \<v>\<a>\<l>[rlte] \<bool>
        \<longmapsto> m \<Ztypecolon> Tickmap\<heavy_comma> j \<Ztypecolon> \<v>\<a>\<l> \<int>\<heavy_comma> m j \<Ztypecolon> \<v>\<a>\<l> \<bool> \<s>\<u>\<b>\<j> j.
             (if lte then j \<le> i \<and> (\<forall>k \<in> {j..<i}. \<not> m k)
                     else i < j \<and> (\<forall>k \<in> {i<..<j}. \<not> m k)) \<rbrace> \<close>

end