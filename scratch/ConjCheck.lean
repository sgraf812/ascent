import Std.WP
open Std.WP
-- Is WPConjunctive visible via the plain `Std.WP` import Ascent uses?
#check @WPConjunctive
#check @WPConjunctive.wp_meet_wp_le
#check @StateT.instWPConjunctive
