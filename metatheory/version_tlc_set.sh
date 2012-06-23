# modify the number by hand and then execute the script
svn propset svn:externals 'tlc -r 174 svn://scm.gforge.inria.fr/svn/tlc/branches/v3' .
cd tlc
svn up
