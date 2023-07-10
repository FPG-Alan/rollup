import b from './b.js';

import('./c').then(module => {
	console.log(module);
});

b();
console.log('a.js');
