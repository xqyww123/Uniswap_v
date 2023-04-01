theory UniSWP_TickBitmap
  imports UniSWP_Common
begin

(*will be a good case to test our \<phi>-type-fiction conversion.
Get fiction relation from \<phi>-type relation.*)

type_synonym tick_map = \<open>tick \<Rightarrow> bool\<close>

resource_space tick_bitmap =
  ticks :: \<open>UNIV::ticks_resource set\<close> (nonsepable_mono_resource)
  by (standard; simp add: set_eq_iff image_iff)

end