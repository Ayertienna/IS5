TLC Library
===========

Author: Arthur Charguéraud


Download
--------

To get the trunk version, run:
   svn checkout svn://scm.gforge.inria.fr/svn/tlc/trunk

To get a stable version, run:
   svn checkout svn://scm.gforge.inria.fr/svn/tlc/branches/v3


Contents
--------

- Lib*.v      => the files from the library
- Lib*Demos.v => some demos showing how tactics work
- Makefile    => used to compile the project
- LICENSE.txt => explains that the files are covered by LGPL
- README.txt  => the current file


Compilation
-----------

Requires Coq-v8.3pl1 to compile. For faster compilation on
 dual core processors, use "make -j" instead of "make".

- make         => compiles everything
- make lib     => compiles everything but the demos
- make demo    => compiles only the demos
- make tactics => compiles only LibTactics and its demos
 

Using the library
-----------------

Write in your file one of the following

- Require Import LibCore.     => to get all the working files of the library
- Require Import LibTactics.  => to get the tactics


Running the demos
-----------------

Run the following commands.

- make tactics
- coqide LibDemoTactics.v &


