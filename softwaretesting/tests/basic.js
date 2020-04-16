const test = require('ava');
const garden = require('../plantgarden')

test('create empty planting decision', t => {
	plant_decision = garden.create_plant_decision(0);
	t.is(plant_decision.length, 0);
});

test('create two length planting decision', t => {
	plant_decision = garden.create_plant_decision(2);
	t.is(plant_decision.length, 2);
	t.deepEqual(plant_decision[0], new Array(new Object()));
	t.deepEqual(plant_decision[1], new Array(new Object()));
});

test('zero round, harvest nothing', t => {
	units = garden.garden_plant_reap_and_collect( 0, garden.create_plant_decision(0) );
	t.is(units.cot, 0);
	t.is(units.crn, 0);
	t.is(units.tto, 0);
});


test('multiple round, no planting, harvest nothing', t => {
	units = garden.garden_plant_reap_and_collect( 1000, garden.create_plant_decision(1000) );
	t.is(units.cot, 0);
	t.is(units.crn, 0);
	t.is(units.tto, 0);
});


test('one round, plant, carrot', t => {
	units = garden.garden_plant_reap_and_collect( 1, [[{ cot: 1 }]] );
	t.is(units.cot, 0);
	t.is(units.crn, 0);
	t.is(units.tto, 0);
});


test('two round, plant, carrot', t => {
	units = garden.garden_plant_reap_and_collect( 2, [[{ cot: 1 }], [{}]] );
	t.is(units.cot, 2);
	t.is(units.crn, 0);
	t.is(units.tto, 0);
});


test('101 round, plant, carrot', t => {
	decisions = garden.create_plant_decision(101);
	decisions[0] = [{cot: 5}];
	units = garden.garden_plant_reap_and_collect( 101, decisions );
	t.is(units.cot, 2);
	t.is(units.crn, 0);
	t.is(units.tto, 0);
});

test('one round, plant, corn', t => {
	units = garden.garden_plant_reap_and_collect( 1, [[{ crn: 1 }]] );
	t.is(units.cot, 0);
	t.is(units.crn, 0);
	t.is(units.tto, 0);
});

test('two round, plant, corn', t => {
	units = garden.garden_plant_reap_and_collect( 2, [[{ crn: 1 }], [{}]] );
	t.is(units.cot, 0);
	t.is(units.crn, 0);
	t.is(units.tto, 0);
});

test('three round, plant, corn', t => {
	units = garden.garden_plant_reap_and_collect( 3, [[{ crn: 1 }], [{}], [{}]] );
	t.is(units.cot, 0);
	t.is(units.crn, 0);
	t.is(units.tto, 0);
});

test('four round, plant, corn', t => {
	units = garden.garden_plant_reap_and_collect( 4, [[{ crn: 1 }], [{}], [{}], [{}]] );
	t.is(units.cot, 0);
	t.is(units.crn, 0);
	t.is(units.tto, 0);
});

test('five round, plant, corn', t => {
	units = garden.garden_plant_reap_and_collect( 5, [[{ crn: 1 }], [{}], [{}], [{}], [{}]] );
	t.is(units.cot, 0);
	t.is(units.crn, 7);
	t.is(units.tto, 0);
});

test('101 round, plant, corn', t => {
	decisions = garden.create_plant_decision(101);
	decisions[0] = [{crn: 1}];
	units = garden.garden_plant_reap_and_collect( 101, decisions );
	t.is(units.cot, 0);
	t.is(units.crn, 7);
	t.is(units.tto, 0);
});

test('one round, plant, tomato', t => {
	units = garden.garden_plant_reap_and_collect( 1, [[{ tto: 1 }]] );
	t.is(units.cot, 0);
	t.is(units.crn, 0);
	t.is(units.tto, 0);
});

test('two round, plant, tomato', t => {
	units = garden.garden_plant_reap_and_collect( 2, [[{ tto: 1 }], [{}]] );
	t.is(units.cot, 0);
	t.is(units.crn, 0);
	t.is(units.tto, 0);
});

test('three round, plant, tomato', t => {
	units = garden.garden_plant_reap_and_collect( 3, [[{ tto: 1 }], [{}], [{}]] );
	t.is(units.cot, 0);
	t.is(units.crn, 0);
	t.is(units.tto, 0);
});

test('four round, plant, tomato', t => {
	decisions = garden.create_plant_decision(4);
	decisions[0] = [{tto: 1}];
	units = garden.garden_plant_reap_and_collect( 4, decisions );
	t.is(units.cot, 0);
	t.is(units.crn, 0);
	t.is(units.tto, 3);
});

test('101 round, plant, tomato', t => {
	decisions = garden.create_plant_decision(101);
	decisions[0] = [{tto: 5}];
	units = garden.garden_plant_reap_and_collect( 101, decisions );
	t.is(units.cot, 0);
	t.is(units.crn, 0);
	t.is(units.tto, 3);
});

test('37 round, plant, each', t => {
	decisions = garden.create_plant_decision(37);
	decisions[0] = [{tto: 1, cot: 3, crn: 5}];
	units = garden.garden_plant_reap_and_collect( 37, decisions );
	t.is(units.cot, 2);
	t.is(units.crn, 7);
	t.is(units.tto, 3);
});

test('37 round, plant carrot at round 37', t => {
	decisions = garden.create_plant_decision(37);
	decisions[36] = [{cot: 5}];
	units = garden.garden_plant_reap_and_collect( 37, decisions);
	t.is(units.cot, 0);
	t.is(units.crn, 0);
	t.is(units.tto, 0);
});

test('carrot next to a carrot', t => {
	decisions = garden.create_plant_decision(4);
	decisions[0] = [{cot: 1, crn: 2}];
	units = garden.garden_plant_reap_and_collect( 4, decisions);
	t.is(units.cot, 3);
	t.is(units.crn, 0);
	t.is(units.tto, 0);
});

test('carrot next to a corn', t => {
	decisions = garden.create_plant_decision(4);
	decisions[0] = [{cot: 1, crn: 2}];
	units = garden.garden_plant_reap_and_collect( 4, decisions);
	t.is(units.cot, 3);
	t.is(units.crn, 0);
	t.is(units.tto, 0);
});

test('carrot next to a tomato', t => {
	decisions = garden.create_plant_decision(4);
	decisions[0] = [{cot: 1, tto: 2}];
	units = garden.garden_plant_reap_and_collect( 4, decisions);
	t.is(units.cot, 1);
	t.is(units.crn, 0);
	t.is(units.tto, 3);
});

test('carrot next to a tomato and tomato next to a carrot', t => {
	decisions = garden.create_plant_decision(4);
	decisions[0] = [{cot: 1, tto: 2}];
	decisions[2] = [{cot: 1}];
	units = garden.garden_plant_reap_and_collect( 4, decisions);
	t.is(units.cot, 2);
	t.is(units.crn, 0);
	t.is(units.tto, 5);
});

test('corn next to a carrot', t => {
	decisions = garden.create_plant_decision(5);
	decisions[0] = [{crn: 2}];
	decisions[4] = [{cot: 1}];
	units = garden.garden_plant_reap_and_collect( 5, decisions);
	t.is(units.cot, 0);
	t.is(units.crn, 8);
	t.is(units.tto, 0);
});

test('corn next to a corn', t => {
	decisions = garden.create_plant_decision(5);
	decisions[0] = [{crn: 2}, {crn: 1}];
	units = garden.garden_plant_reap_and_collect( 5, decisions);
	t.is(units.cot, 0);
	t.is(units.crn, 12);
	t.is(units.tto, 0);
});

test('corn next to a tomato', t => {
	decisions = garden.create_plant_decision(5);
	decisions[0] = [{crn: 2}];
	decisions[1] = [{tto: 1}];
	units = garden.garden_plant_reap_and_collect( 5, decisions);
	t.is(units.cot, 0);
	t.is(units.crn, 9);
	t.is(units.tto, 4);
});

test('replant carrot each turn', t => {
	decisions = garden.create_plant_decision(4);
	decisions[0] = [{cot: 1}];
	decisions[1] = [{cot: 1}];
	decisions[2] = [{cot: 1}];
	decisions[3] = [{cot: 1}];
	units = garden.garden_plant_reap_and_collect( 4, decisions);
	t.is(units.cot, 0);
	t.is(units.crn, 0);
	t.is(units.tto, 0);
});

test('all carrot', t => {
	decisions = garden.create_plant_decision(4);
	decisions[0] = [{cot: 1}, {cot: 2}, {cot: 3}, {cot: 4}, {cot: 5}];
	units = garden.garden_plant_reap_and_collect( 4, decisions);
	t.is(units.cot, 2);
	t.is(units.crn, 0);
	t.is(units.tto, 0);
});

test('all corn', t => {
	decisions = garden.create_plant_decision(5);
	decisions[0] = [{crn: 1}, {crn: 2}, {crn: 3}, {crn: 4}, {crn: 5}];
	units = garden.garden_plant_reap_and_collect( 5, decisions);
	t.is(units.cot, 0);
	t.is(units.crn, 27);
	t.is(units.tto, 0);
});

test('all tomato', t => {
	decisions = garden.create_plant_decision(5);
	decisions[0] = [{tto: 1}, {tto: 2}, {tto: 3}, {tto: 4}, {tto: 5}];
	units = garden.garden_plant_reap_and_collect( 5, decisions);
	t.is(units.cot, 0);
	t.is(units.crn, 0);
	t.is(units.tto, 7);
});

test('all corn and tomato', t => {
	decisions = garden.create_plant_decision(5);
	decisions[0] = [{crn: 1},           {crn: 3},           {crn: 5}];
	decisions[1] = [          {tto: 2},           {tto: 4},         ];
	units = garden.garden_plant_reap_and_collect( 5, decisions);
	t.is(units.cot, 0);
	t.is(units.crn, 29);
	t.is(units.tto, 10);
});

