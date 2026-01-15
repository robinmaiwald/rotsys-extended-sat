__IMPORTANT NOTE__
________________________________________________________________________________________________________________________________________________________

The SAT-framework in this project was originally designed by Manfred Scheucher (and Helena Bergold). 
Link to the original project which is cloned: https://github.com/manfredscheucher/rotsys-sat/tree/main  
All credit for the creation of this framework belongs to him (and her).
________________________________________________________________________________________________________________________________________________________

I used this framework to study properties of almost complete graphs (complete graphs missing a matching) for my bachelor's thesis.
To do this I extended the framework by creating additional parameters.  
The difference between this project and the one on Manfred's Scheucher GitHub is that I added additional parameters to rotsys.py.
SO here is what I did:  
I cloned his project and added rotsys-extension.py - an extension of his version of rotsys.py.
For transparency, I left the original rotsys.py.
I did this so I could link the project in my thesis and in case someone is interested in the additional parameters.  

________________________________________________________________________________________________________________________________________________________

The following parameters have been added by me (version from 1.9.2025).

-fixMUp       : Given a matching (I)  and a upper bound (U) for crossings -> With this you can search for a Kn-I with cr(Kn-I) <= U  
-fixMLow       : Given a matching (I)  and a upper bound (L) for crossings -> With this you can search for a Kn-I with cr(Kn-I) >= L  
-twoColor      : Parameter which can be used to allow 2-color crossings (disabled by default)  

-goodOcta      : Given a lower bound (L) -> This ensures there are at least L crossings in all induced octahedrons, default value is 1   
-octaFix       : Given a value (k)       -> This ensures there is at least one induced octahedron with k crossings  
-goodCross     : Given a value (k)       -> This ensures there are at least k good (4-color) crossings when you connect a Kn - I with an apex vertex - I is a perfect matching  


_______________________________________________________________________________________________________________________________________________________

The parameters -fixMUp, -fixMLow, -twoColor are for complete graphs missing a matching quite useful.  
The parameter -goodOcta, -octaFix, -goodCross were designed for a very specific use and might not be usefull for others.  
In all my code I tried to use Manfred Scheucher's style. I am sure there are parts which can be made "more efficent". 
________________________________________________________________________________________________________________________________________________________

I added my program generate_matchings.py.
Given n,k this program generates all possible matchings I, |I| = k from the complete graph Kn.
They get saved to a txt file called matchings_"n"v_"k"e.txt.



