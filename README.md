# Coq Plugin smpl

A plugin that realizes a tactic similar to `first [ l_1 | ... | l_n ]`,
with the twist that the list `l_1 | ... | l_n` can be extended like an
eauto database.

See [the included demo file](theories/Demo.v).