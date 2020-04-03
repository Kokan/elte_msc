

module.exports.garden_plant_reap_and_collect = function(number_of_rounds, planting_decisions)
{
  if (number_of_rounds == 0) {
  return {
    cot: 0,
    crn: 0,
    tto: 0,
  };
  };

  var cot = 0;
  var crn = 0;
  var tto = 0;

  if (planting_decisions.length > 0 && planting_decisions[0].cot > 0) {
    cot =  Math.floor(number_of_rounds/2)*2
  }

  if (planting_decisions.length > 0 && planting_decisions[0].crn > 0) {
    crn = Math.floor(number_of_rounds/5)*7
  }

  if (planting_decisions.length > 0 && planting_decisions[0].tto > 0) {
    tto = Math.floor(number_of_rounds/4)*3
  }

  return {
    cot: cot,
    crn: crn,
    tto: tto,
  };
}

