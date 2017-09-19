# Coq Plugin smpl

Smpl is useful for proof automation in Coq. Smpl provides named lists
of tactics to which tactics can be added with Coq commands. A special
tactic called 'smpl foo' executes the tactics in the lists named foo
in order, until one of them succeeds. Smpl works across modules by
merging tactics from all imports according to a priority number that
can be provided upon addition. Smpl thus allows to modify the behavior
of a tactic after it is defined in a convenient and modular way.

Put differently, Smpl realizes a tactic that behaves similarily to 

    first [ l_1 | ... | l_n]
        
with the twist that the list `l_1 | ... | l_n` can be extended
in a fashion akin to eauto database (i.e. adding tactics works
across modules by merging the lists).

The plugin is available for Coq 8.6.1 in branch v8.6 and for 8.7 in
branch master.

See [the included demo file](theories/Demo.v) for instructions how to
use the plugin.

## Installation

If you are familiar with Coq plugins, this plugin will be no surprise
to you. Simply download the plugin, either by downloading the .zip 
archive here, or cloning the repository. The following command then
install the plugin into the user-contrib directory of your Coq 
installation.

   cd smpl
   make
   make install

In any of your files, you can then simply import the plugin via

    Require Import smpl.Smpl.

### Including smpl in your project 

If you want to place smpl in your project, you can place it
in a directory of your project.

    git clone https://github.com/sigurdschneider/smpl.git
    cd smpl
    make

**Note** that if you are using **Coq 8.6.1**, then you need to instead
use the folloing clone command, which specifies the branch to clone from:

    git clone -b v8.6 https://github.com/sigurdschneider/smpl.git

To use the plugin, you must add the following to your _CoqProject file:

    -R smpl/theories smpl
    -I smpl/src
    
**Important** make sure that smpl is not covered by any other recursive
import command, such as `-R . Foo` as this will result in different module
names and not work.

In any of your files, you can then simply import the plugin via

    Require Import smpl.Smpl.
