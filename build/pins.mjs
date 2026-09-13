export const SOURCE_PINS = Object.freeze({
  lunar: 'd95191818d7975c22613f231fea160341203abbe',
  jpl_eph: 'a73f25e54d02b99b1c0d9a9d6c61acfbb2fa3a26',
  sat_code: '2bbb8cb2e417edb10918e4404464b68e24abcab4',
  find_orb: '9cc932997837c5ab994fbf015db59f5d0da852e5',
});
export const EPHEMERIS = Object.freeze({
  name: 'JPL DE-440',
  filename: 'linux_p1550p2650.440',
  url: 'https://ssd.jpl.nasa.gov/ftp/eph/planets/Linux/de440/linux_p1550p2650.440',
  sha256: '29915576d0a6555766b99485ac3056ee415e86df4fce282611c31afb329ad062',
});
// Installed upstream data, not user preferences or cached previous solutions.
export const DATA_FILES = `bright.pgm bright2.pgm calendar.txt cometdef.sof command.txt cospar.txt
details.txt dosephem.txt dos_help.txt elem_pop.txt environ.def eph2tle.txt eph_expl.txt eph_type.txt
dfindorb.txt efindorb.txt ffindorb.txt ifindorb.txt rfindorb.txt sfindorb.txt
frame_he.txt geo_rect.txt header.htm hints.def jpl_eph.txt link_def.json mpc_area.txt
mpcorb.hdr mu1.txt nongravs.txt obj_help.txt obj_name.txt ObsCodes.htm ObsCodesF.html
observer.htm obslinks.htm odd_name.txt openfile.txt orbitdef.sof previous.def progcode.txt
radecfmt.txt residfmt.txt rovers.txt sat_xref.txt scope.json scopes.txt splash.txt sigma.txt
site_310.txt timehelp.txt xdesig.txt`.split(/\s+/);
export const EMSDK = Object.freeze({version:'4.0.23', commit:'c0bb220cb6e6f4e0fabb6f6db9efd53390ef5e56'});
