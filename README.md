[![CII Best Practices](https://bestpractices.coreinfrastructure.org/projects/4094/badge)](https://bestpractices.coreinfrastructure.org/projects/4094)

checkperms is a small and simple program that detects many
inconsistencies in file and directory permissions. Theoretically, there
are 2^12 valid combinations (setuid, setgid, sticky, owner-rwx,
group-rwx, other-rwx), but only very few of them are actually used.

It can automatically fix the permissions if instructed so.
